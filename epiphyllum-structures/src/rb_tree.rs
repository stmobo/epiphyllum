use alloc::alloc::{handle_alloc_error, AllocError, Allocator, Global, Layout};
use core::{borrow::Borrow, debug_assert};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ptr;
use core::ptr::NonNull;
use core::mem;
use core::ops::{Deref, DerefMut, Bound, RangeBounds};
use core::cmp::Ordering;
use core::sync::atomic::{AtomicPtr, AtomicUsize};
use core::sync::atomic;
use mem::swap;

pub struct RBTree<K, V, Alloc: Allocator = Global> {
    base: ManuallyDrop<BasePointer<K, V, Alloc>>,
    _m1: PhantomData<K>,
    _m2: PhantomData<V>,
    _m3: PhantomData<Alloc>,
}

impl<K, V> RBTree<K, V, Global> {
    pub fn new() -> RBTree<K, V, Global> {
        Self::new_with(Global)
    }
}

impl<K, V, Alloc: Allocator> RBTree<K, V, Alloc> {
    pub fn new_with(allocator: Alloc) -> RBTree<K, V, Alloc> {
        RBTree {
            base: ManuallyDrop::new(BasePointer::new(allocator)),
            _m1: PhantomData,
            _m2: PhantomData,
            _m3: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.base.len()
    }

    fn root(&self) -> Option<NonNull<TreeNode<K, V, Alloc>>> {
        self.base.get_root()
    }

    fn get_node<T>(&self, key: &T) -> Option<NonNull<TreeNode<K, V, Alloc>>>
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        self.root()
            .and_then(|root| unsafe { root.as_ref().find_node(key) })
    }

    pub fn get<T>(&self, key: &T) -> Option<&V>
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        self.get_node(key).map(|p| unsafe { (*p.as_ptr()).val.deref() })
    }

    pub fn get_mut<T>(&mut self, key: &T) -> Option<&mut V>
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        self.get_node(key).map(|p| unsafe { (*p.as_ptr()).val.deref_mut() })
    }

    pub fn contains<T>(&self, key: &T) -> bool
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        self.get_node(key).is_some()
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        if let Some(root) = self.root() {
            TreeNode::insert(root, key, value)
        } else {
            let new_node = Some(TreeNode::alloc_new(self.base.base(), key, value, false, None, None));
            self.base.set_root(new_node);
            self.base.set_first(new_node);
            self.base.set_last(new_node);
            self.base.increment_len();
            None
        }
    }

    pub fn remove<T>(&mut self, key: &T) -> Option<V>
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        unsafe {
            self.get_node(key)
                .map(|mut node| node.as_mut().delete())
                .map(|deleted| TreeNode::cleanup(deleted).1)
        }
    }

    pub fn get_first(&self) -> Option<(&K, &V)>
    {
        self.base.first_node()
            .map(|node| unsafe {
                let node = node.as_ptr();
                ((*node).key.deref(), (*node).val.deref())
            })
    }

    pub fn get_first_mut(&mut self) -> Option<(&K, &mut V)>
    {
        self.base.first_node()
            .map(|node| unsafe {
                let node = node.as_ptr();
                ((*node).key.deref(), (*node).val.deref_mut())
            })
    }

    pub fn pop_first(&mut self) -> Option<(K, V)>
    {
        unsafe {
            self.base.first_node()
                .map(|mut node| node.as_mut().delete())
                .map(|deleted| TreeNode::cleanup(deleted))
        }
    }

    pub fn get_last(&self) -> Option<(&K, &V)>
    {
        self.base.last_node()
            .map(|node| unsafe {
                let node = node.as_ptr();
                ((*node).key.deref(), (*node).val.deref())
            })
    }

    pub fn get_last_mut(&mut self) -> Option<(&K, &mut V)>
    {
        self.base.last_node()
            .map(|node| unsafe {
                let node = node.as_ptr();
                ((*node).key.deref(), (*node).val.deref_mut())
            })
    }

    pub fn pop_last(&mut self) -> Option<(K, V)>
    {
        unsafe {
            self.base.last_node()
                .map(|mut node| node.as_mut().delete())
                .map(|deleted| TreeNode::cleanup(deleted))
        }
    }

    fn node_iter(&self) -> NodeIter<K, V, Alloc> {
        NodeIter {
            fwd: self.base.first_node(),
            back: self.base.last_node()
        }
    }

    fn get_bound_key<T: ?Sized>(bound: Bound<&T>) -> Option<(bool, &T)> {
        match bound {
            Bound::Unbounded => None,
            Bound::Included(k) => Some((false, k)),
            Bound::Excluded(k) => Some((true, k)),
        }
    }

    fn node_iter_range<T, R>(&self, range: R) -> NodeIter<K, V, Alloc>
    where
        K: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized,
    {
        let lkey = Self::get_bound_key(range.start_bound());
        let rkey = Self::get_bound_key(range.end_bound());

        if let Some((lkey, rkey)) = lkey.zip(rkey) {
            match lkey.1.cmp(rkey.1) {
                Ordering::Less => (),
                Ordering::Greater => panic!("invalid range (start > end)"),
                Ordering::Equal => if lkey.0 && rkey.0 {
                    panic!("invalid range (start == end with excluded bounds)")
                }
            }
        }

        self.root().map_or_else(
            || NodeIter { fwd: None, back: None,},
            |root| unsafe {
                let mut fwd = root.as_ref().find_lower_bound(range.start_bound());
                let mut back = root.as_ref().find_upper_bound(range.end_bound());

                if let Some((l, r)) = fwd.zip(back) {
                    if l.as_ref().prev == Some(r) {
                        fwd = None;
                        back = None;
                    }
                } else {
                    fwd = None;
                    back = None;
                }

                NodeIter { fwd, back }
            }
        )
    }

    pub fn iter(&self) -> Iter<'_, K, V, Alloc> {
        Iter {
            it: self.node_iter(),
            _marker: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, Alloc> {
        IterMut {
            it: self.node_iter(),
            _marker: PhantomData,
        }
    }

    pub fn range<T, R>(&self, range: R) -> Iter<'_, K, V, Alloc>
    where
        K: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized
    {
        Iter {
            it: self.node_iter_range(range),
            _marker: PhantomData,
        }
    }

    pub fn range_mut<T, R>(&mut self, range: R) -> IterMut<'_, K, V, Alloc>
    where
        K: Borrow<T>,
        R: RangeBounds<T>,
        T: Ord + ?Sized
    {
        IterMut {
            it: self.node_iter_range(range),
            _marker: PhantomData,
        }
    }
}

unsafe impl<#[may_dangle] K, #[may_dangle] V, Alloc: Allocator> Drop for RBTree<K, V, Alloc> {
    fn drop(&mut self) {
        unsafe { drop(ptr::read(self).into_iter()) }
    }
}

pub struct BasePointer<K, V, Alloc: Allocator = Global>(NonNull<TreeBase<K, V, Alloc>>);

impl<K, V, Alloc: Allocator> BasePointer<K, V, Alloc> {
    fn new(allocator: Alloc) -> BasePointer<K, V, Alloc> {
        let layout = Layout::new::<TreeBase<K, V, Alloc>>();
        let dst: Result<NonNull<[u8]>, AllocError> = allocator.allocate(layout);

        if let Ok(dst) = dst {
            let p: NonNull<TreeBase<K, V, Alloc>> = dst.cast();
            unsafe {
                p.as_ptr().write(TreeBase::new(allocator));
            }

            BasePointer(p)
        } else {
            handle_alloc_error(layout)
        }
    }

    fn base(&self) -> NonNull<TreeBase<K, V, Alloc>> {
        self.0
    }
}

impl<K, V, Alloc: Allocator> Deref for BasePointer<K, V, Alloc> {
    type Target = TreeBase<K, V, Alloc>;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

unsafe impl<#[may_dangle] K, #[may_dangle] V, Alloc: Allocator> Drop for BasePointer<K, V, Alloc> {
    fn drop(&mut self) {
        unsafe {
            let mut p = self.0;
            let allocator = ManuallyDrop::take(&mut p.as_mut().allocator);

            ptr::drop_in_place(p.as_ptr());
            allocator.deallocate(p.cast(), Layout::new::<TreeBase<K, V, Alloc>>());
        }
    }
}

unsafe impl<K, V, Alloc: Allocator> Send for BasePointer<K, V, Alloc> {}
unsafe impl<K, V, Alloc: Allocator> Sync for BasePointer<K, V, Alloc> {}

pub struct SyncPtr<T>(AtomicPtr<T>);

impl<T> SyncPtr<T> {
    pub fn new() -> SyncPtr<T> {
        SyncPtr(AtomicPtr::new(ptr::null_mut()))
    }

    pub fn set(&self, new_val: Option<NonNull<T>>) {
        let p = new_val.map_or(ptr::null_mut(), |p| p.as_ptr());
        self.0.store(p, atomic::Ordering::SeqCst);
    }

    pub fn get(&self) -> Option<NonNull<T>> {
        NonNull::new(self.0.load(atomic::Ordering::SeqCst))
    }
}

pub struct TreeBase<K, V, Alloc: Allocator = Global> {
    root: SyncPtr<TreeNode<K, V, Alloc>>,
    first: SyncPtr<TreeNode<K, V, Alloc>>,
    last: SyncPtr<TreeNode<K, V, Alloc>>,
    len: AtomicUsize,
    allocator: ManuallyDrop<Alloc>
}

impl<K, V, Alloc: Allocator> TreeBase<K, V, Alloc> {
    fn new(allocator: Alloc) -> TreeBase<K, V, Alloc> {
        TreeBase {
            allocator: ManuallyDrop::new(allocator),
            root: SyncPtr::new(),
            first: SyncPtr::new(),
            last: SyncPtr::new(),
            len: AtomicUsize::new(0),
        }
    }

    fn set_root(&self, node: Option<NonNull<TreeNode<K, V, Alloc>>>) {
        self.root.set(node)
    }

    fn get_root(&self) -> Option<NonNull<TreeNode<K, V, Alloc>>> {
        self.root.get()
    }

    fn set_first(&self, node: Option<NonNull<TreeNode<K, V, Alloc>>>) {
        self.first.set(node);
    }

    fn first_node(&self) -> Option<NonNull<TreeNode<K, V, Alloc>>> {
        self.first.get()
    }

    fn set_last(&self, node: Option<NonNull<TreeNode<K, V, Alloc>>>) {
        self.last.set(node);
    }

    fn last_node(&self) -> Option<NonNull<TreeNode<K, V, Alloc>>> {
        self.last.get()
    }

    fn increment_len(&self) {
        self.len.fetch_add(1, atomic::Ordering::SeqCst);
    }

    fn decrement_len(&self) {
        assert!(self.len.fetch_sub(0, atomic::Ordering::SeqCst) > 0, "node count underflow");
    }

    fn len(&self) -> usize {
        self.len.load(atomic::Ordering::SeqCst)
    }
}

pub struct TreeNode<K, V, Alloc: Allocator = Global> {
    parent: Option<NonNull<TreeNode<K, V, Alloc>>>,
    left: Option<NonNull<TreeNode<K, V, Alloc>>>,
    right: Option<NonNull<TreeNode<K, V, Alloc>>>,
    prev: Option<NonNull<TreeNode<K, V, Alloc>>>,
    next: Option<NonNull<TreeNode<K, V, Alloc>>>,
    tree: NonNull<TreeBase<K, V, Alloc>>,
    color: bool, // true = red
    key: ManuallyDrop<K>,
    val: ManuallyDrop<V>,
}

impl<K, V, Alloc: Allocator> TreeNode<K, V, Alloc> {
    fn alloc_new(
        tree: NonNull<TreeBase<K, V, Alloc>>,
        key: K,
        val: V,
        color: bool,
        prev: Option<NonNull<TreeNode<K, V, Alloc>>>,
        next: Option<NonNull<TreeNode<K, V, Alloc>>>,
    ) -> NonNull<TreeNode<K, V, Alloc>> {
        let layout = Layout::new::<TreeNode<K, V, Alloc>>();
        let dst: Result<NonNull<[u8]>, AllocError> = unsafe { (*tree.as_ptr()).allocator.allocate(layout) };

        if let Ok(dst) = dst {
            let p: NonNull<TreeNode<K, V, Alloc>> = dst.cast();
            unsafe {
                p.as_ptr().write(TreeNode {
                    parent: None,
                    left: None,
                    right: None,
                    prev,
                    next,
                    color,
                    tree,
                    key: ManuallyDrop::new(key),
                    val: ManuallyDrop::new(val),
                });
            }

            p
        } else {
            handle_alloc_error(layout)
        }
    }

    unsafe fn cleanup(mut node: NonNull<TreeNode<K, V, Alloc>>) -> (K, V) {
        let layout = Layout::new::<TreeNode<K, V, Alloc>>();
        let tree = (*node.as_ptr()).tree.as_ptr();
        let kv = {
            let d = node.as_mut();
            let key = ManuallyDrop::take(&mut d.key);
            let val = ManuallyDrop::take(&mut d.val);
            (key, val)
        };

        ptr::drop_in_place(node.as_ptr());
        (*tree).allocator.deallocate(node.cast(), layout);

        if (*tree).get_root() == Some(node) {
            (*tree).set_root(None);
        }

        (*tree).decrement_len();

        kv
    }

    fn with_parent_sibling<'s, 'a, F, R>(&'s mut self, func: F) -> R
    where
        's: 'a,
        F: FnOnce(&'s mut TreeNode<K, V, Alloc>, Option<&'a mut TreeNode<K, V, Alloc>>, Option<&'a mut TreeNode<K, V, Alloc>>, bool) -> R
    {
        let self_ptr = NonNull::new(self as *mut Self);
        debug_assert!(self_ptr.is_some());

        let (sibling_ptr, is_left) = self.parent.map_or((None, false), |p| {
            unsafe {
                let p = p.as_ptr();
                if (*p).left == self_ptr {
                    ((*p).right, true)
                } else {
                    ((*p).left, false)
                }
            }
        });

        let sibling_ref = sibling_ptr.map(|p| unsafe { &mut (*p.as_ptr()) });
        let parent_ref = self.parent.map(|p| unsafe { &mut (*p.as_ptr()) });

        func(self, parent_ref, sibling_ref, is_left)
    }

    fn left_ref(&self) -> Option<&TreeNode<K, V, Alloc>> {
        self.left.map(|p| unsafe { &(*p.as_ptr()) })
    }

    fn right_ref(&self) -> Option<&TreeNode<K, V, Alloc>> {
        self.right.map(|p| unsafe { &(*p.as_ptr()) })
    }

    fn left_mut(&mut self) -> Option<&mut TreeNode<K, V, Alloc>> {
        self.left.map(|p| unsafe { &mut (*p.as_ptr()) })
    }

    fn right_mut(&mut self) -> Option<&mut TreeNode<K, V, Alloc>> {
        self.right.map(|p| unsafe { &mut (*p.as_ptr()) })
    }

    fn prev_mut(&mut self) -> Option<&mut TreeNode<K, V, Alloc>> {
        self.prev.map(|p| unsafe { &mut (*p.as_ptr()) })
    }

    fn next_mut(&mut self) -> Option<&mut TreeNode<K, V, Alloc>> {
        self.next.map(|p| unsafe { &mut (*p.as_ptr()) })
    }

    fn leftmost(&self) -> NonNull<TreeNode<K, V, Alloc>> {
        if let Some(left) = self.left_ref() {
            left.leftmost()
        } else {
            self.into()
        }
    }

    fn rightmost(&self) -> NonNull<TreeNode<K, V, Alloc>> {
        if let Some(right) = self.right_ref() {
            right.rightmost()
        } else {
            self.into()
        }
    }

    fn set_left_child(&mut self, child: Option<&mut TreeNode<K, V, Alloc>>) {
        if let Some(r) = child {
            r.parent = NonNull::new(self as *mut Self);
            debug_assert!(r.parent.is_some());
            self.left = Some(NonNull::from(r));
        } else {
            self.left = None;
        }
    }

    fn set_right_child(&mut self, child: Option<&mut TreeNode<K, V, Alloc>>) {
        if let Some(r) = child {
            r.parent = NonNull::new(self as *mut Self);
            debug_assert!(r.parent.is_some());
            self.right = Some(NonNull::from(r));
        } else {
            self.right = None;
        }
    }

    unsafe fn make_self_root(&mut self) {
        let self_ptr = NonNull::new(self as *mut Self);
        self.tree.as_ref().set_root(self_ptr);
    }

    fn is_left_child(parent: &TreeNode<K, V, Alloc>, child: &TreeNode<K, V, Alloc>) -> bool {
        parent.left.map_or(false, |p| ptr::eq(p.as_ptr(), child))
    }

    fn rotate(parent: &mut TreeNode<K, V, Alloc>, pivot: &mut TreeNode<K, V, Alloc>, grandparent: Option<&mut TreeNode<K, V, Alloc>>) {
        let gp_link = grandparent.map(|gp| {
            let is_left = Self::is_left_child(gp, parent);
            (gp, is_left)
        });

        if Self::is_left_child(parent, pivot) {
            // Right rotation
            parent.set_left_child(pivot.right_mut());
            pivot.set_right_child(Some(parent));
        } else {
            // Left rotation
            parent.set_right_child(pivot.left_mut());
            pivot.set_left_child(Some(parent));
        }

        if let Some((gp, parent_was_left)) = gp_link {
            if parent_was_left {
                gp.set_left_child(Some(pivot));
            } else {
                gp.set_right_child(Some(pivot));
            }
        } else {
            pivot.parent = None;
            unsafe { pivot.make_self_root() }
        }
    }

    fn repair_insert(&mut self) {
        if self.parent.is_none() {
            self.color = false;
            return;
        }

        self.with_parent_sibling(|s, parent, _, self_is_left| {
            let parent = parent.unwrap();
            if !parent.color {
                /* If parent node is black, then tree is still valid */
                return;
            }

            /* Parent is red, therefore we must have a grandparent. */
            parent.with_parent_sibling(|mut parent, gp, uncle, parent_is_left| {
                let gp = gp.unwrap();
                if let Some(uncle) = uncle {
                    if uncle.color {
                        parent.color = false;
                        uncle.color = false;
                        gp.color = true;
                        return gp.repair_insert();
                    }
                }

                let mut child = s;
                if self_is_left != parent_is_left {
                    Self::rotate(parent, child, Some(gp));
                    swap(&mut child, &mut parent);
                }

                gp.with_parent_sibling(|gp, ggp, _, _| {
                    Self::rotate(gp, parent, ggp);
                });
                parent.color = false;
                gp.color = true;
            });
        });
    }

    fn swap_data(&mut self, other: &mut TreeNode<K, V, Alloc>) {
        swap(&mut self.key, &mut other.key);
        swap(&mut self.val, &mut other.val);
    }

    fn delete(&mut self) -> NonNull<TreeNode<K, V, Alloc>> {
        if self.left.is_some() && self.right.is_some() {
            let successor = unsafe { &mut (*self.next.unwrap().as_ptr()) };
            self.swap_data(successor);
            return successor.delete();
        }

        if !self.color {
            if self.left.is_some() || self.right.is_some() {
                self.with_parent_sibling(|s, parent, _, is_left| {
                    let child = if s.left.is_some() {
                        s.left_mut()
                    } else {
                        s.right_mut()
                    }.unwrap();

                    child.color = false;

                    if let Some(parent) = parent {
                        if is_left {
                            parent.set_left_child(Some(child));
                        } else {
                            parent.set_right_child(Some(child));
                        }
                    } else {
                        child.parent = None;
                        unsafe { child.make_self_root() };
                    }
                });

                self.parent = None;
            } else {
                self.delete_fix();
            }
        }

        if self.parent.is_some() {
            self.with_parent_sibling(|_, parent, _, is_left| {
                if is_left {
                    parent.unwrap().set_left_child(None);
                } else {
                    parent.unwrap().set_right_child(None);
                }
            });
        }

        let next = self.next;
        let prev = self.prev;

        if let Some(prev) = self.prev_mut() {
            prev.next = next;
        } else {
            unsafe { self.tree.as_ref().set_first(next) };
        }

        if let Some(next) = self.next_mut() {
            next.prev = prev;
        } else {
            unsafe { self.tree.as_ref().set_last(prev) };
        }

        NonNull::new(self as *mut Self).unwrap()
    }

    fn delete_fix_2(&mut self) {
        self.with_parent_sibling(|_, parent, sibling, is_left| {
            let parent = parent.unwrap();
            let sibling = sibling.unwrap();

            sibling.color = parent.color;
            parent.color = false;

            {
                let c = if is_left {
                    sibling.right_mut()
                } else {
                    sibling.left_mut()
                };

                if let Some(c) = c {
                    c.color = false;
                }
            }

            parent.with_parent_sibling(|parent, gp, _, _| {
                Self::rotate(parent, sibling, gp)
            })
        })
    }

    fn delete_fix(&mut self) {
        if self.parent.is_none() {
            return;
        }

        self.with_parent_sibling(|_, parent, sibling, _| {
            let parent = parent.unwrap();

            if let Some(sibling) = sibling {
                if sibling.color {
                    parent.color = true;
                    sibling.color = false;
                    parent.with_parent_sibling(|parent, gp, _, _| {
                        Self::rotate(parent, sibling, gp);
                    })
                }
            }
        });

        self.with_parent_sibling(|s, parent, sibling, is_left| {
            let parent = parent.unwrap();
            let sibling = sibling.unwrap();

            let sib_left_black = sibling.left_ref().map_or(true, |r| !r.color);
            let sib_right_black = sibling.right_ref().map_or(true, |r| !r.color);

            if !parent.color && !sibling.color && sib_left_black && sib_right_black {
                sibling.color = true;
                return parent.delete_fix();
            }

            if parent.color && !sibling.color && sib_left_black && sib_right_black {
                sibling.color = true;
                parent.color = false;
                return;
            }

            if !sibling.color {
                if is_left && !sib_left_black && sib_right_black {
                    sibling.color = true;
                    let c = unsafe { &mut (*sibling.left.unwrap().as_ptr()) };
                    c.color = false;
                    Self::rotate(sibling, c, Some(parent));
                } else if !is_left && sib_left_black && !sib_right_black {
                    sibling.color = true;
                    let c = unsafe { &mut (*sibling.right.unwrap().as_ptr()) };
                    c.color = false;
                    Self::rotate(sibling, c, Some(parent));
                }
            }

            s.delete_fix_2()
        });
    }

    fn find_node<T>(&self, key: &T) -> Option<NonNull<TreeNode<K, V, Alloc>>>
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        match key.cmp(self.key.deref().borrow()) {
            Ordering::Equal => Some(self.into()),
            Ordering::Less => {
                self.left_ref().and_then(|r| r.find_node(key))
            },
            Ordering::Greater => {
                self.right_ref().and_then(|r| r.find_node(key))
            }
        }
    }

    fn find_insert_position(&self, key: &K,
        prev: Option<NonNull<TreeNode<K, V, Alloc>>>,
        next: Option<NonNull<TreeNode<K, V, Alloc>>>
    ) -> (Ordering, NonNull<TreeNode<K, V, Alloc>>, Option<NonNull<TreeNode<K, V, Alloc>>>, Option<NonNull<TreeNode<K, V, Alloc>>>)
    where
        K: Ord
    {
        let self_ptr: NonNull<TreeNode<K, V, Alloc>> = NonNull::from(self);
        match key.cmp(self.key.deref().borrow()) {
            Ordering::Equal => (Ordering::Equal, self_ptr, prev, next),
            Ordering::Less => {
                self.left_ref().map_or(
                    (Ordering::Less, self_ptr, prev, Some(self_ptr)),
                
                    |r| r.find_insert_position(key, prev, Some(self_ptr))
                )
            },
            Ordering::Greater => {
                self.right_ref().map_or(
                    (Ordering::Greater, self_ptr, Some(self_ptr), next),
                    |r| r.find_insert_position(key, Some(self_ptr), next)
                )
            }
        }
    }

    fn insert(root: NonNull<TreeNode<K, V, Alloc>>, key: K, mut val: V) -> Option<V>
    where
        K: Ord,
    {
        let (cmp, mut parent, prev, next) = unsafe { root.as_ref().find_insert_position(&key, None, None) };

        if cmp == Ordering::Equal {
            let r = unsafe { parent.as_mut() };
            swap(r.val.deref_mut(), &mut val);
            return Some(val);
        }

        let tree = unsafe { root.as_ref().tree };
        let mut new_node = Self::alloc_new(tree, key, val, true, prev, next);

        unsafe {
            match cmp {
                Ordering::Equal => unreachable!("equal cmp"),
                Ordering::Less => {
                    parent.as_mut().set_left_child(Some(new_node.as_mut()));
                },
                Ordering::Greater => {
                    parent.as_mut().set_right_child(Some(new_node.as_mut()));
                },
            }

            new_node.as_mut().repair_insert();

            if let Some(mut prev) = prev {
                prev.as_mut().next = Some(new_node);
            } else {
                tree.as_ref().set_first(Some(new_node));
            }

            if let Some(mut next) = next {
                next.as_mut().prev = Some(new_node);
            } else {
                tree.as_ref().set_last(Some(new_node));
            }

            tree.as_ref().increment_len();
        }

        None
    }

    fn find_lower_bound<T>(&self, bound: Bound<&T>) -> Option<NonNull<TreeNode<K, V, Alloc>>> 
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        match bound {
            Bound::Unbounded => Some(self.leftmost()),
            Bound::Included(key) => match key.cmp(self.key.deref().borrow()) {
                Ordering::Equal => Some(NonNull::from(self)),
                Ordering::Less => self.left_ref().map_or(
                    Some(NonNull::from(self)),
                    |r| r.find_lower_bound(bound)
                ),
                Ordering::Greater => self.right_ref().map_or(
                    self.next,
                    |r| r.find_lower_bound(bound)
                ),
            },
            Bound::Excluded(key) => match key.cmp(self.key.deref().borrow()) {
                Ordering::Less => self.left_ref().map_or(
                    Some(NonNull::from(self)),
                    |r| r.find_lower_bound(bound)
                ),
                Ordering::Greater | Ordering::Equal => self.right_ref().map_or(
                    self.next,
                    |r| r.find_lower_bound(bound)
                ),
            },
        }
    }

    fn find_upper_bound<T>(&self, bound: Bound<&T>) -> Option<NonNull<TreeNode<K, V, Alloc>>> 
    where
        K: Borrow<T>,
        T: Ord + ?Sized,
    {
        match bound {
            Bound::Unbounded => Some(self.rightmost()),
            Bound::Included(key) => match key.cmp(self.key.deref().borrow()) {
                Ordering::Equal => Some(NonNull::from(self)),
                Ordering::Less => self.left_ref().map_or(
                    self.prev,
                    |r| r.find_upper_bound(bound)
                ),
                Ordering::Greater => self.right_ref().map_or(
                    Some(NonNull::from(self)),
                    |r| r.find_upper_bound(bound)
                ),
            },
            Bound::Excluded(key) => match key.cmp(self.key.deref().borrow()) {
                Ordering::Less | Ordering::Equal => self.left_ref().map_or(
                    self.prev,
                    |r| r.find_upper_bound(bound)
                ),
                Ordering::Greater => self.right_ref().map_or(
                    Some(NonNull::from(self)),
                    |r| r.find_upper_bound(bound)
                ),
            },
        }
    }
}

pub struct NodeIter<K, V, Alloc: Allocator> {
    fwd: Option<NonNull<TreeNode<K, V, Alloc>>>,
    back: Option<NonNull<TreeNode<K, V, Alloc>>>,
}

impl<K, V, Alloc: Allocator> Iterator for NodeIter<K, V, Alloc> {
    type Item = NonNull<TreeNode<K, V, Alloc>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.fwd.map(|p| {
            if self.fwd != self.back {
                self.fwd = unsafe { p.as_ref().next };
            } else {
                self.fwd = None;
                self.back = None;
            }

            p
        })
    }
}

impl<K, V, Alloc: Allocator> DoubleEndedIterator for NodeIter<K, V, Alloc> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.back.map(|p| {
            if self.back != self.fwd {
                self.back = unsafe { p.as_ref().prev };
            } else {
                self.fwd = None;
                self.back = None;
            }

            p
        })
    }
}


pub struct IntoIter<K, V, Alloc: Allocator> {
    it: NodeIter<K, V, Alloc>,
    _bp: BasePointer<K, V, Alloc>,
}

impl<K, V, Alloc: Allocator> Iterator for IntoIter<K, V, Alloc> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.it
            .next()
            .map(|node| unsafe { TreeNode::cleanup(node) })
    }
}

impl<K, V, Alloc: Allocator> DoubleEndedIterator for IntoIter<K, V, Alloc> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.it
            .next_back()
            .map(|node| unsafe { TreeNode::cleanup(node) })
    }
}

unsafe impl<#[may_dangle] K, #[may_dangle] V, Alloc: Allocator> Drop for IntoIter<K, V, Alloc> {
    fn drop(&mut self) {
        while self.next().is_some() {}
    }
}

impl<K, V, Alloc: Allocator> IntoIterator for RBTree<K, V, Alloc> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, Alloc>;

    fn into_iter(self) -> Self::IntoIter {
        /* Wrap self in ManuallyDrop to avoid recursing, since RBTree's Drop
         * impl calls this function */
        let mut s = ManuallyDrop::new(self);

        IntoIter {
            it: s.node_iter(),
            _bp: unsafe { ManuallyDrop::take(&mut s.base) },
        }
    }
}

pub struct Iter<'a, K, V, Alloc: Allocator> {
    it: NodeIter<K, V, Alloc>,
    _marker: PhantomData<&'a RBTree<K, V, Alloc>>,
}

impl<'a, K, V, Alloc: Allocator> Iterator for Iter<'a, K, V, Alloc> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next().map(|p| unsafe {
            let p = p.as_ptr();
            ((*p).key.deref(), (*p).val.deref())
        })
    }
}

impl<'a, K, V, Alloc: Allocator> DoubleEndedIterator for Iter<'a, K, V, Alloc> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.it.next_back().map(|p| unsafe {
            let p = p.as_ptr();
            ((*p).key.deref(), (*p).val.deref())
        })
    }
}

pub struct IterMut<'a, K, V, Alloc: Allocator> {
    it: NodeIter<K, V, Alloc>,
    _marker: PhantomData<&'a mut RBTree<K, V, Alloc>>,
}

impl<'a, K, V, Alloc: Allocator> Iterator for IterMut<'a, K, V, Alloc> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next().map(|p| unsafe {
            let p = p.as_ptr();
            ((*p).key.deref(), (*p).val.deref_mut())
        })
    }
}

impl<'a, K, V, Alloc: Allocator> DoubleEndedIterator for IterMut<'a, K, V, Alloc> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.it.next_back().map(|p| unsafe {
            let p = p.as_ptr();
            ((*p).key.deref(), (*p).val.deref_mut())
        })
    }
}



#[cfg(test)]
mod tests {
    use super::RBTree;
    use core::cell::RefCell;
    use core::cmp::Ordering;
    use core::fmt::Debug;
    use core::hash::Hash;
    use core::{alloc::Allocator, ops::Deref};
    use alloc::collections::BTreeMap;
    use quickcheck::TestResult;
    use std::{collections::BTreeSet, collections::HashMap, prelude::v1::*};
    use core::ops::Bound;

    use super::TreeNode;

    #[allow(dead_code)]
    fn print_recursive<K: Debug, V: Debug, Alloc: Allocator>(
        node: &TreeNode<K, V, Alloc>,
        level: usize,
    ) {
        if let Some(right) = node.right_ref() {
            print_recursive(right, level + 1);
        }

        for _ in 0..level {
            print!("       ");
        }

        if node.color {
            println!("{:?}: {:?} (R)", node.key.deref(), node.val.deref());
        } else {
            println!("{:?}: {:?} (B)", node.key.deref(), node.val.deref());
        }

        if let Some(left) = node.left_ref() {
            print_recursive(left, level + 1);
        }
    }

    fn verify_node_correctness<K, V, Alloc>(
        node: &TreeNode<K, V, Alloc>,
        seen: &mut HashMap<K, V>,
    ) -> Result<usize, ()>
    where
        K: Hash + Eq + Copy,
        V: Copy,
        Alloc: Allocator,
    {
        if seen.contains_key(&node.key) {
            return Err(());
        }

        seen.insert(*node.key, *node.val);

        let left_blk_height = node.left_ref().map_or(Ok(1), |p| {
            verify_node_correctness(p, seen)
        })?;

        let right_blk_height = node.right_ref().map_or(Ok(1), |p| {
            verify_node_correctness(p, seen)
        })?;

        if left_blk_height != right_blk_height {
            Err(())
        } else if node.color {
            let left_is_blk = node.left_ref().map_or(true, |p| !p.color);
            let right_is_blk = node.right_ref().map_or(true, |p| !p.color);

            if left_is_blk && right_is_blk {
                Ok(left_blk_height)
            } else {
                Err(())
            }
        } else {
            Ok(left_blk_height + 1)
        }
    }

    fn verify_tree_correctness<K, V, Alloc>(tree: &RBTree<K, V, Alloc>) -> bool
    where
        K: Hash + Eq + Copy,
        V: Copy,
        Alloc: Allocator,
    {
        if let Some(root) = tree.base.get_root() {
            let mut hm = HashMap::new();
            verify_node_correctness(unsafe { &(*root.as_ptr()) }, &mut hm).is_ok()
        } else {
            true
        }
    }

    #[test]
    fn test_insert() {
        let keys: Vec<u64> = vec![1, 5, 3, 6, 4, 2];
        let vals: Vec<u64> = vec![1, 2, 3, 4, 5, 6];
        let mut tree = RBTree::new();

        for (k, v) in keys.iter().copied().zip(vals.iter().copied()) {
            tree.insert(k, v);            
        }

        for (k, v) in keys.iter().copied().zip(vals.iter().copied()) {
            assert_eq!(tree.get(&k).map(|r| *r), Some(v))
        }

        assert_eq!(tree.len(), keys.len());
    }

    #[test]
    fn test_remove() {
        let mut keys: Vec<u64> = vec![1, 5, 3, 6, 4, 2];
        let mut vals: Vec<u64> = vec![1, 2, 3, 4, 5, 6];
        let mut tree = RBTree::new();

        for (k, v) in keys.iter().copied().zip(vals.iter().copied()) {
            tree.insert(k, v);
        }

        keys.reverse();
        vals.reverse();

        let n = keys.len();
        for _ in 0..n - 1 {
            let k = keys.pop().unwrap();
            assert_eq!(tree.remove(&k), vals.pop());

            for (k, v) in keys.iter().copied().zip(vals.iter().copied()) {
                assert_eq!(tree.get(&k).map(|r| *r), Some(v))
            }

            assert_eq!(tree.len(), keys.len());
        }
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn do_quickcheck(mut vals: Vec<(u64, u64)>, del: Vec<usize>) -> TestResult {
        if vals.len() < del.len() {
            return TestResult::discard();
        }

        let mut tree = RBTree::new();
        let mut hm = HashMap::new();

        for (k, v) in vals.iter().copied() {
            tree.insert(k, v);
            hm.insert(k, v);

            if !verify_tree_correctness(&tree) {
                return TestResult::failed();
            }

            if tree.len() != hm.len() {
                return TestResult::failed();
            }
        }

        for i in del.iter().copied() {
            let i = i % vals.len();
            let (k, _) = vals.swap_remove(i);

            if tree.get(&k).copied() != hm.get(&k).copied() {
                return TestResult::failed();
            }

            if tree.remove(&k) != hm.remove(&k) {
                return TestResult::failed();
            }

            if tree.get(&k).is_some() {
                return TestResult::failed();
            }
            
            if tree.len() != hm.len() {
                return TestResult::failed();
            }

            if !verify_tree_correctness(&tree) {
                return TestResult::failed();
            }
        }

        TestResult::passed()
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_iter(vals: Vec<u64>) -> bool {
        let mut tree = RBTree::new();
        let mut model = BTreeSet::new();

        for v in vals.iter().copied() {
            tree.insert(v, ());
            model.insert(v);
        }

        let t1: Vec<u64> = model.iter().copied().collect();
        let t2: Vec<u64> = tree.iter().map(|kv| *(kv.0)).collect();

        t1 == t2
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_range_iter(vals: Vec<u64>, lb: Bound<u64>, ub: Bound<u64>) -> TestResult {
        let k1 = match lb {
            Bound::Unbounded => None,
            Bound::Included(k) => Some((false, k)),
            Bound::Excluded(k) => Some((true, k)),
        };

        let k2 = match ub {
            Bound::Unbounded => None,
            Bound::Included(k) => Some((false, k)),
            Bound::Excluded(k) => Some((true, k)),
        };

        if let Some((k1, k2)) = k1.zip(k2) {
            match k1.1.cmp(&k2.1) {
                Ordering::Less => (),
                Ordering::Greater => return TestResult::discard(),
                Ordering::Equal => if k1.0 && k2.0 { return TestResult::discard() }
            }
        }

        let mut tree = RBTree::new();
        let mut model = BTreeSet::new();

        for v in vals.iter().copied() {
            tree.insert(v, ());
            model.insert(v);
        }

        let t1: Vec<u64> = model.range((lb, ub)).copied().collect();
        let t2: Vec<u64> = tree.range((lb, ub)).map(|kv| *(kv.0)).collect();

        TestResult::from_bool(t1 == t2)
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_into_iter(vals: Vec<u64>) -> bool {
        let mut tree = RBTree::new();
        let mut model = BTreeSet::new();

        for v in vals.iter().copied() {
            tree.insert(v, ());
            model.insert(v);
        }

        let t1: Vec<u64> = model.iter().copied().collect();
        let t2: Vec<u64> = tree.into_iter().map(|kv| kv.0).collect();

        t1 == t2
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_iter_mut(vals: Vec<u64>) -> bool {
        let mut tree = RBTree::new();
        let mut model = BTreeSet::new();

        for v in vals.iter().copied() {
            tree.insert(v, vals.len() + 1);
            model.insert(v);
        }

        for (i, kv) in tree.iter_mut().enumerate() {
            let (_, v) = kv;
            *v = i;
        }

        let t1: Vec<(usize, u64)> = model.iter().copied().enumerate().collect();
        let t2: Vec<(usize, u64)> = tree.iter().map(|kv| (*kv.1, *kv.0)).collect();

        t1 == t2
    }

    struct AddOnDrop<'a>(&'a RefCell<BTreeSet<u64>>, u64);

    impl<'a> Drop for AddOnDrop<'a> {
        fn drop(&mut self) {
            self.0.borrow_mut().insert(self.1);
        }
    }

    impl<'a> PartialOrd for AddOnDrop<'a> {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.1.partial_cmp(&other.1)
        }
    }

    impl<'a> Ord for AddOnDrop<'a> {
        fn cmp(&self, other: &Self) -> Ordering {
            self.1.cmp(&other.1)
        }
    }

    impl<'a> PartialEq for AddOnDrop<'a> {
        fn eq(&self, other: &Self) -> bool {
            self.1 == other.1
        }
    }

    impl<'a> Eq for AddOnDrop<'a> {}

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_drop(kvs: Vec<(u64, u64)>) -> bool {
        let mut expected_keys = BTreeSet::new();
        let mut expected_vals = BTreeSet::new();
        let drop_keys = RefCell::new(BTreeSet::new());
        let drop_vals = RefCell::new(BTreeSet::new());

        {
            let mut tree = RBTree::new();
            for (k, v) in kvs.iter().copied() {
                tree.insert(AddOnDrop(&drop_keys, k), AddOnDrop(&drop_vals, v));
                expected_keys.insert(k);
                expected_vals.insert(v);
            }
        }

        let t1: Vec<u64> = expected_keys.iter().copied().collect();
        let t2: Vec<u64> = drop_keys.into_inner().iter().copied().collect();
        let t3: Vec<u64> = expected_vals.iter().copied().collect();
        let t4: Vec<u64> = drop_vals.into_inner().iter().copied().collect();

        (t1 == t2) && (t3 == t4)
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_get_first(mut vals: Vec<(u64, u64)>) -> bool {
        let mut tree = RBTree::new();
        let mut model = BTreeMap::new();

        for (k, v) in vals.iter().copied() {
            tree.insert(k, v);
            model.insert(k, v);
        }

        vals.sort_by(|a, b| a.0.cmp(&b.0));
        
        let expected = vals
            .get(0)
            .and_then(|kv| model.get_key_value(&kv.0))
            .map(|kv| (*kv.0, *kv.1));

        tree.get_first().map(|kv| (*kv.0, *kv.1)) == expected
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_get_first_mut(mut vals: Vec<u64>, x: u64) -> TestResult {
        if vals.len() == 0 {
            return TestResult::discard();
        }

        let mut tree = RBTree::new();

        for k in vals.iter().copied() {
            tree.insert(k, 0);
        }

        if let Some((_, v)) = tree.get_first_mut() {
            *v = x;
        }

        vals.sort_by(|a, b| a.cmp(b));
        
        TestResult::from_bool(tree.get(&vals[0]).copied() == tree.get_first().map(|r| *r.1))
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_pop_first(vals: Vec<(u64, u64)>) -> TestResult {
        let mut tree = RBTree::new();
        let mut model = BTreeMap::new();

        for (k, v) in vals.iter().copied() {
            tree.insert(k, v);
            model.insert(k, v);
        }

        let expected: Vec<(u64, u64)> = model.into_iter().collect();
        let mut actual: Vec<(u64, u64)> = Vec::with_capacity(expected.len());

        let mut cur = tree.pop_first();
        while cur.is_some() {
            actual.push(cur.unwrap());
            cur = tree.pop_first();
        }

        TestResult::from_bool(expected == actual)
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_get_last(mut vals: Vec<(u64, u64)>) -> bool {
        let mut tree = RBTree::new();
        let mut model = BTreeMap::new();

        for (k, v) in vals.iter().copied() {
            tree.insert(k, v);
            model.insert(k, v);
        }
        
        vals.sort_by(|a, b| a.0.cmp(&b.0).reverse());

        let expected = vals
            .get(0)
            .and_then(|kv| model.get_key_value(&kv.0))
            .map(|kv| (*kv.0, *kv.1));

        tree.get_last().map(|kv| (*kv.0, *kv.1)) == expected
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_get_last_mut(mut vals: Vec<u64>, x: u64) -> TestResult {
        if vals.len() == 0 {
            return TestResult::discard();
        }

        let mut tree = RBTree::new();

        for k in vals.iter().copied() {
            tree.insert(k, 0);
        }

        if let Some((_, v)) = tree.get_last_mut() {
            *v = x;
        }

        vals.sort_by(|a, b| a.cmp(b).reverse());
        
        TestResult::from_bool(tree.get(&vals[0]).copied() == tree.get_last().map(|r| *r.1))
    }

    #[cfg_attr(miri, ignore)]
    #[quickcheck]
    fn quickcheck_pop_last(vals: Vec<(u64, u64)>) -> TestResult {
        let mut tree = RBTree::new();
        let mut model = BTreeMap::new();

        for (k, v) in vals.iter().copied() {
            tree.insert(k, v);
            model.insert(k, v);
        }

        let expected: Vec<(u64, u64)> = model.into_iter().rev().collect();
        let mut actual: Vec<(u64, u64)> = Vec::with_capacity(expected.len());

        let mut cur = tree.pop_last();
        while cur.is_some() {
            actual.push(cur.unwrap());
            cur = tree.pop_last();
        }

        TestResult::from_bool(expected == actual)
    }
}
