use alloc::alloc::Layout;
use core::ops::{Deref, DerefMut};
use core::ptr;

#[derive(Debug)]
#[repr(transparent)]
pub struct AVLTree<T, K: Ord> {
    root: *mut AVLTreeNode<T, K>,
}

impl<T, K: Ord> AVLTree<T, K> {
    pub fn new() -> AVLTree<T, K> {
        AVLTree {
            root: ptr::null_mut(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.root == ptr::null_mut()
    }

    pub fn successor(&self, key: K) -> Option<(&K, &T)> {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            let successor_node = (*self.root).find_successor(key);
            if successor_node != ptr::null_mut() {
                let key = &(*successor_node).key;
                let data = (*successor_node).data.as_ref().unwrap();

                Some((key, data))
            } else {
                None
            }
        }
    }

    pub fn successor_mut(&mut self, key: K) -> Option<(&K, &mut T)> {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            let successor_node = (*self.root).find_successor(key);
            if successor_node != ptr::null_mut() {
                let key = &(*successor_node).key;
                let data = (*successor_node).data.as_mut().unwrap();

                Some((key, data))
            } else {
                None
            }
        }
    }

    pub fn predecessor(&self, key: K) -> Option<(&K, &T)> {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            let predecessor_node = (*self.root).find_predecessor(key);
            if predecessor_node != ptr::null_mut() {
                let key = &(*predecessor_node).key;
                let data = (*predecessor_node).data.as_ref().unwrap();

                Some((key, data))
            } else {
                None
            }
        }
    }

    pub fn predecessor_mut(&mut self, key: K) -> Option<(&K, &mut T)> {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            let predecessor_node = (*self.root).find_predecessor(key);
            if predecessor_node != ptr::null_mut() {
                let key = &(*predecessor_node).key;
                let data = (*predecessor_node).data.as_mut().unwrap();

                Some((key, data))
            } else {
                None
            }
        }
    }

    pub fn find_first<P, R>(&self, mapper: P) -> Option<R>
    where
        P: Fn(&T) -> Option<R>,
    {
        unsafe {
            if self.root != ptr::null_mut() {
                (*self.root).find_first(&mapper)
            } else {
                None
            }
        }
    }

    pub fn delete(&mut self, key: K) -> Option<T> {
        use alloc::alloc::dealloc;
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            let p = (*self.root).search(key);
            if p != ptr::null_mut() {
                let (new_root, ret) = (*p).remove();
                self.root = new_root;

                let layout = Layout::new::<AVLTreeNode<T, K>>();
                ptr::drop_in_place(p);
                dealloc(p as *mut u8, layout);

                return Some(ret);
            }
        }

        None
    }

    /// Get a reference to a value within this tree.
    ///
    /// `key_func` must be a function that maps values within this tree
    /// to non-overlapping intervals; this function will return the value
    /// whose interval contains `key`, if it exists within the tree.
    pub fn search_interval<F>(&self, key: K, key_func: F) -> Option<&T>
    where
        F: Fn(&T) -> (K, K),
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe { (*self.root).search_interval(key, &key_func).map(|r| &*r) }
    }

    /// Get a reference to a value within this tree.
    pub fn search(&self, key: K) -> Option<&T> {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            let p = (*self.root).search(key);
            if p != ptr::null_mut() {
                (*p).data.as_ref()
            } else {
                None
            }
        }
    }

    /// Look up a value by interval in this tree and get a mutable reference to it.
    pub fn search_interval_mut<F>(&mut self, key: K, key_func: F) -> Option<&mut T>
    where
        F: Fn(&T) -> (K, K),
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe { (*self.root).search_interval(key, &key_func) }
    }

    /// Look up a value in this tree and get a mutable reference to it.
    pub fn search_mut(&mut self, key: K) -> Option<&mut T> {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            let p = (*self.root).search(key);
            if p != ptr::null_mut() {
                (*p).data.as_mut()
            } else {
                None
            }
        }
    }

    /// Insert a new node into this tree.
    ///
    /// Returns a reference to the inserted element.
    pub fn insert(&mut self, key: K, data: T) -> &mut T {
        if self.root != ptr::null_mut() {
            let (new_root, elem) = unsafe { (*self.root).insert(key, data) };
            self.root = new_root;
            elem.data.as_mut().unwrap()
        } else {
            unsafe {
                self.root = AVLTreeNode::<T, K>::new_alloc(key, data);
                (*self.root).data.as_mut().unwrap()
            }
        }
    }
}

impl<T, K: Ord> Drop for AVLTree<T, K> {
    fn drop(&mut self) {
        use alloc::alloc::dealloc;

        let layout = Layout::new::<AVLTreeNode<T, K>>();
        unsafe {
            if self.root != ptr::null_mut() {
                ptr::drop_in_place(self.root);
                dealloc(self.root as *mut u8, layout);
            }
        }
    }
}

unsafe impl<T, K: Ord> Send for AVLTree<T, K> {}
unsafe impl<T, K: Ord> Sync for AVLTree<T, K> {}

#[derive(Debug)]
pub struct AVLTreeNode<T, K: Ord> {
    key: K,
    data: Option<T>,
    parent: *mut AVLTreeNode<T, K>,
    left: *mut AVLTreeNode<T, K>,
    right: *mut AVLTreeNode<T, K>,
    balance: i8,
}

impl<T, K: Ord> Deref for AVLTreeNode<T, K> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.data.as_ref().unwrap()
    }
}

impl<T, K: Ord> DerefMut for AVLTreeNode<T, K> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data.as_mut().unwrap()
    }
}

impl<T, K: Ord> AVLTreeNode<T, K> {
    unsafe fn new_alloc(key: K, data: T) -> *mut AVLTreeNode<T, K> {
        use alloc::alloc::alloc;

        let layout = Layout::new::<AVLTreeNode<T, K>>();
        let new_node = alloc(layout) as *mut AVLTreeNode<T, K>;
        ptr::write(
            new_node,
            AVLTreeNode {
                key,
                data: Some(data),
                parent: ptr::null_mut(),
                left: ptr::null_mut(),
                right: ptr::null_mut(),
                balance: 0,
            },
        );

        new_node
    }

    unsafe fn find_first<P, R>(&mut self, mapper: &P) -> Option<R>
    where
        P: Fn(&T) -> Option<R>,
    {
        if let Some(result) = mapper(self.data.as_mut().unwrap()) {
            return Some(result);
        }

        if self.left != ptr::null_mut() {
            if let Some(result) = (*self.left).find_first(mapper) {
                return Some(result);
            }
        }

        if self.right != ptr::null_mut() {
            if let Some(result) = (*self.right).find_first(mapper) {
                return Some(result);
            }
        }

        None
    }

    fn search_interval<F>(&mut self, key: K, key_func: &F) -> Option<&mut T>
    where
        K: Ord,
        F: Fn(&T) -> (K, K),
    {
        unsafe {
            let (key_ival_start, key_ival_end) = key_func(self.data.as_ref().unwrap());
            if key >= key_ival_start && key < key_ival_end {
                return self.data.as_mut();
            }

            if key < key_ival_start {
                if self.left != ptr::null_mut() {
                    (*self.left).search_interval(key, key_func)
                } else {
                    None
                }
            } else {
                if self.right != ptr::null_mut() {
                    (*self.right).search_interval(key, key_func)
                } else {
                    None
                }
            }
        }
    }

    fn search(&mut self, key: K) -> *mut AVLTreeNode<T, K> {
        use core::cmp::Ordering;

        unsafe {
            match key.cmp(&self.key) {
                Ordering::Equal => self as *mut AVLTreeNode<T, K>,
                Ordering::Less => {
                    if self.left != ptr::null_mut() {
                        (*self.left).search(key)
                    } else {
                        ptr::null_mut()
                    }
                }
                Ordering::Greater => {
                    if self.right != ptr::null_mut() {
                        (*self.right).search(key)
                    } else {
                        ptr::null_mut()
                    }
                }
            }
        }
    }

    fn find_successor(&mut self, key: K) -> *mut AVLTreeNode<T, K> {
        use core::cmp::Ordering;

        match key.cmp(&self.key) {
            Ordering::Equal => self as *mut AVLTreeNode<T, K>,
            Ordering::Less => {
                if self.left != ptr::null_mut() {
                    unsafe { (*self.left).find_successor(key) }
                } else {
                    self as *mut AVLTreeNode<T, K>
                }
            }
            Ordering::Greater => {
                if self.right != ptr::null_mut() {
                    unsafe { (*self.right).find_successor(key) }
                } else {
                    self.successor()
                }
            }
        }
    }

    fn find_predecessor(&mut self, key: K) -> *mut AVLTreeNode<T, K> {
        use core::cmp::Ordering;

        match key.cmp(&self.key) {
            Ordering::Equal => self as *mut AVLTreeNode<T, K>,
            Ordering::Less => {
                if self.left != ptr::null_mut() {
                    unsafe { (*self.left).find_predecessor(key) }
                } else {
                    self.predecessor()
                }
            }
            Ordering::Greater => {
                if self.right != ptr::null_mut() {
                    unsafe { (*self.right).find_predecessor(key) }
                } else {
                    self as *mut AVLTreeNode<T, K>
                }
            }
        }
    }

    fn leftmost(&mut self) -> *mut AVLTreeNode<T, K> {
        unsafe {
            if self.left == ptr::null_mut() {
                return self as *mut AVLTreeNode<T, K>;
            } else {
                return (*self.left).leftmost();
            }
        }
    }

    fn rightmost(&mut self) -> *mut AVLTreeNode<T, K> {
        unsafe {
            if self.right == ptr::null_mut() {
                return self as *mut AVLTreeNode<T, K>;
            } else {
                return (*self.right).rightmost();
            }
        }
    }

    /// Remove this node from the tree.
    unsafe fn remove(&mut self) -> (*mut AVLTreeNode<T, K>, T) {
        let self_ptr = self as *mut AVLTreeNode<T, K>;

        let replacement: *mut AVLTreeNode<T, K>;
        let retrace_from: *mut AVLTreeNode<T, K>;

        if self.left != ptr::null_mut() && self.right != ptr::null_mut() {
            /* Two children */
            let replacement_child: *mut AVLTreeNode<T, K>;
            let replacement_parent: *mut AVLTreeNode<T, K>;

            if self.balance <= 0 {
                /* Replace with in-order successor node */
                replacement = (*self.right).leftmost();
                replacement_child = (*replacement).right;
                replacement_parent = (*replacement).parent;

                (*replacement).left = self.left;
                (*self.left).parent = replacement;

                if replacement != self.right {
                    (*replacement_parent).left = replacement_child;
                    retrace_from = replacement_child;
                } else {
                    retrace_from = replacement;
                }
            } else {
                /* Replace with in-order predecessor node */
                replacement = (*self.left).rightmost();
                replacement_child = (*replacement).left;
                replacement_parent = (*replacement).parent;

                (*replacement).right = self.right;
                (*self.right).parent = replacement;

                if replacement != self.left {
                    (*replacement_parent).right = replacement_child;
                    retrace_from = replacement_child;
                } else {
                    retrace_from = replacement;
                }
            }

            /* Move replacement's child (if any) into replacement's old position */
            if replacement_parent != self_ptr && replacement_child != ptr::null_mut() {
                (*replacement_child).parent = replacement_parent;
            }
        } else if self.left != ptr::null_mut() {
            /* One child */
            replacement = self.left;
            retrace_from = replacement;
        } else if self.right != ptr::null_mut() {
            /* ditto */
            replacement = self.right;
            retrace_from = replacement;
        } else {
            /* No children */
            replacement = ptr::null_mut();
            retrace_from = self.parent;
        }

        if replacement != ptr::null_mut() {
            (*replacement).parent = self.parent;

            if replacement != self.right {
                (*replacement).right = self.right;
                if self.right != ptr::null_mut() {
                    (*self.right).parent = replacement;
                }
            }

            if replacement != self.left {
                (*replacement).left = self.left;
                if self.left != ptr::null_mut() {
                    (*self.left).parent = replacement;
                }
            }
        }

        if self.parent != ptr::null_mut() {
            if (*self.parent).left == self_ptr {
                (*self.parent).left = replacement;
            } else {
                (*self.parent).right = replacement;
            }
        }

        assert_ne!(retrace_from, ptr::null_mut());
        let new_root = (*retrace_from).retrace_delete();
        self.parent = ptr::null_mut();
        self.left = ptr::null_mut();
        self.right = ptr::null_mut();

        (new_root, self.data.take().unwrap())
    }

    unsafe fn retrace_delete(&mut self) -> *mut AVLTreeNode<T, K> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTreeNode<T, K>;
        }

        let prev_parent = self.parent;
        if (*self.parent).right == (self as *mut AVLTreeNode<T, K>) {
            /* Right subtree has decreased in height */

            if (*self.parent).balance < 0 {
                /* Parent is left-heavy. */
                let sibling = (*self.parent).left;
                let b = (*sibling).balance;

                if (*sibling).balance <= 0 {
                    (*self.parent).right_rotate();
                } else {
                    let prev_parent = self.parent;
                    (*sibling).left_rotate();
                    (*prev_parent).right_rotate();
                }

                if b != 0 {
                    return (*prev_parent).retrace_delete();
                }
            } else {
                /* Tree is still balanced. */
                (*self.parent).balance -= 1;
                if (*self.parent).balance == 0 {
                    /* Need to continue retracing. */
                    return (*self.parent).retrace_insert();
                }

                /* Otherwise, tree is balanced */
                return self.recurse_to_root();
            }
        } else {
            /* Left subtree has decreased in height */
            if (*self.parent).balance > 0 {
                /* Parent is right-heavy. */
                let sibling = (*self.parent).right;
                let b = (*sibling).balance;

                if (*sibling).balance >= 0 {
                    (*self.parent).left_rotate();
                } else {
                    let prev_parent = self.parent;
                    (*sibling).right_rotate();
                    (*prev_parent).left_rotate();
                }

                if b != 0 {
                    return (*prev_parent).retrace_delete();
                }
            } else {
                (*self.parent).balance += 1;
                if (*self.parent).balance == 0 {
                    return (*self.parent).retrace_insert();
                }

                return self.recurse_to_root();
            }
        }

        self.recurse_to_root()
    }

    /// Insert a new node into this tree.
    ///
    /// Returns a tuple consisting of:
    ///   - a pointer to the new root node, and
    ///   - a reference to the inserted element.
    fn insert(&mut self, key: K, data: T) -> (*mut AVLTreeNode<T, K>, &mut AVLTreeNode<T, K>) {
        let mut cur: *mut AVLTreeNode<T, K> = self as *mut AVLTreeNode<T, K>;
        let new_node: *mut AVLTreeNode<T, K>;

        unsafe {
            new_node = AVLTreeNode::<T, K>::new_alloc(key, data);
        }

        loop {
            unsafe {
                let r1 = &(*new_node).key;
                let r2 = &(*cur).key;

                if *r1 < *r2 {
                    if (*cur).left != ptr::null_mut() {
                        cur = (*cur).left;
                    } else {
                        /* Insert as left subtree. */
                        (*cur).left = new_node;
                        break;
                    }
                } else {
                    if (*cur).right != ptr::null_mut() {
                        cur = (*cur).right;
                    } else {
                        (*cur).right = new_node;
                        break;
                    }
                }
            }
        }

        unsafe {
            (*new_node).parent = cur;
            let new_parent = (*new_node).retrace_insert();
            (new_parent, &mut *new_node)
        }
    }

    unsafe fn right_rotate(&mut self) -> *mut AVLTreeNode<T, K> {
        let pivot = self.left;

        if pivot != ptr::null_mut() {
            self.left = (*pivot).right;
            (*pivot).right = self as *mut AVLTreeNode<T, K>;

            if self.left != ptr::null_mut() {
                (*self.left).parent = self as *mut AVLTreeNode<T, K>;
            }

            let prev_parent = self.parent;
            if prev_parent != ptr::null_mut() {
                if (*prev_parent).left == (self as *mut AVLTreeNode<T, K>) {
                    (*prev_parent).left = pivot;
                } else {
                    (*prev_parent).right = pivot;
                }
            }

            (*pivot).parent = prev_parent;
            self.parent = pivot;

            if (*pivot).balance == 0 {
                self.balance = -1;
                (*pivot).balance = 1;
            } else {
                self.balance = 0;
                (*pivot).balance = 0;
            }
        }

        pivot
    }

    unsafe fn left_rotate(&mut self) -> *mut AVLTreeNode<T, K> {
        let pivot = self.right;

        if pivot != ptr::null_mut() {
            self.right = (*pivot).left;
            (*pivot).left = self as *mut AVLTreeNode<T, K>;

            if self.right != ptr::null_mut() {
                (*self.right).parent = self as *mut AVLTreeNode<T, K>;
            }

            let prev_parent = self.parent;
            if prev_parent != ptr::null_mut() {
                if (*prev_parent).left == (self as *mut AVLTreeNode<T, K>) {
                    (*prev_parent).left = pivot;
                } else {
                    (*prev_parent).right = pivot;
                }
            }

            (*pivot).parent = prev_parent;
            self.parent = pivot;

            if (*pivot).balance == 0 {
                self.balance = 1;
                (*pivot).balance = -1;
            } else {
                self.balance = 0;
                (*pivot).balance = 0;
            }
        }

        pivot
    }

    fn recurse_to_root(&mut self) -> *mut AVLTreeNode<T, K> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTreeNode<T, K>;
        } else {
            unsafe { (*self.parent).recurse_to_root() }
        }
    }

    /// Retracing loop after subtree height increases.
    ///
    /// Returns the new overall root of the tree.
    unsafe fn retrace_insert(&mut self) -> *mut AVLTreeNode<T, K> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTreeNode<T, K>;
        }

        let prev_parent = self.parent;
        if (*self.parent).right == (self as *mut AVLTreeNode<T, K>) {
            /* We are right-hand child: */

            if (*self.parent).balance > 0 {
                /* Tree is unbalanced at parent. */
                if self.balance >= 0 {
                    /* Right-Right case. */
                    (*self.parent).left_rotate();
                } else {
                    /* Right-Left case. */
                    self.right_rotate();
                    (*prev_parent).left_rotate();
                }
            } else {
                /* Tree is still balanced. */
                (*self.parent).balance += 1;
                if (*self.parent).balance == 1 {
                    /* Need to continue retracing. */
                    return (*self.parent).retrace_insert();
                }

                /* Otherwise, tree is perfectly balanced-- don't need to do anything further! */
            }
        } else {
            /* We are left-hand child: */
            if (*self.parent).balance < 0 {
                if self.balance <= 0 {
                    /* Left-Left case. */
                    (*self.parent).right_rotate();
                } else {
                    /* Left-Right case. */
                    self.left_rotate();
                    (*prev_parent).right_rotate();
                }
            } else {
                (*self.parent).balance -= 1;
                if (*self.parent).balance == -1 {
                    return (*self.parent).retrace_insert();
                }
            }
        }

        self.recurse_to_root()
    }

    fn successor(&mut self) -> *mut AVLTreeNode<T, K> {
        unsafe {
            if self.right != ptr::null_mut() {
                return (*self.right).leftmost();
            } else if self.parent != ptr::null_mut() {
                let mut cur = self as *mut AVLTreeNode<T, K>;
                while (*cur).parent != ptr::null_mut() {
                    let parent = (*cur).parent;
                    if (*parent).left == cur {
                        return parent;
                    }
                    cur = parent;
                }
            }
            ptr::null_mut()
        }
    }

    fn predecessor(&mut self) -> *mut AVLTreeNode<T, K> {
        unsafe {
            if self.left != ptr::null_mut() {
                return (*self.left).rightmost();
            } else if self.parent != ptr::null_mut() {
                let mut cur = self as *mut AVLTreeNode<T, K>;
                while (*cur).parent != ptr::null_mut() {
                    let parent = (*cur).parent;
                    if (*parent).right == cur {
                        return parent;
                    }
                    cur = parent;
                }
            }
            ptr::null_mut()
        }
    }
}

impl<T, K: Ord> Drop for AVLTreeNode<T, K> {
    fn drop(&mut self) {
        use alloc::alloc::dealloc;

        let layout = Layout::new::<AVLTreeNode<T, K>>();
        unsafe {
            if let Some(data) = self.data.take() {
                drop(data);
            }

            if self.left != ptr::null_mut() {
                ptr::drop_in_place(self.left);
                dealloc(self.left as *mut u8, layout);
            }

            if self.right != ptr::null_mut() {
                ptr::drop_in_place(self.right);
                dealloc(self.right as *mut u8, layout);
            }
        }
    }
}
