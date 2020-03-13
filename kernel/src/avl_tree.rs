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

    pub fn traverse<F>(&self, f: F)
    where
        F: Fn(&K, &T) -> (),
    {
        if self.root != ptr::null_mut() {
            unsafe {
                return (*self.root).inorder_traversal(&f);
            }
        }
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

    unsafe fn inorder_traversal<F>(&self, func: &F)
    where
        F: Fn(&K, &T) -> (),
    {
        if self.left != ptr::null_mut() {
            (*self.left).inorder_traversal(func);
        }

        func(&self.key, self.data.as_ref().unwrap());

        if self.right != ptr::null_mut() {
            return (*self.right).inorder_traversal(func);
        }
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
            Ordering::Equal => self.successor(),
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

        match self.key.cmp(&key) {
            Ordering::Equal => self.predecessor(),
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

    fn set_balance(&mut self, balance: i8) {
        self.balance = balance;

        if cfg!(debug_assertions) {
            if balance < 0 {
                assert_ne!(
                    self.left,
                    ptr::null_mut(),
                    "attempt to set balance < 0 with null left child"
                );
            } else if balance > 0 {
                assert_ne!(
                    self.right,
                    ptr::null_mut(),
                    "attempt to set balance > 0 with null right child"
                );
            }
        }
    }

    /// Remove this node from the tree.
    unsafe fn remove(&mut self) -> (*mut AVLTreeNode<T, K>, T) {
        let self_ptr = self as *mut AVLTreeNode<T, K>;

        assert_ne!(self.left, self_ptr);
        assert_ne!(self.right, self_ptr);
        assert_ne!(self.parent, self_ptr);

        let replacement: *mut AVLTreeNode<T, K>;
        let retrace_from: *mut AVLTreeNode<T, K>;

        let mut replacement_child: *mut AVLTreeNode<T, K> = ptr::null_mut();
        let mut replacement_parent: *mut AVLTreeNode<T, K> = ptr::null_mut();
        let mut update_replacement_side = false;
        let two_children: bool;

        if self.left != ptr::null_mut() && self.right != ptr::null_mut() {
            /* Two children */
            two_children = true;

            if self.balance <= 0 {
                /* Replace with in-order successor node */
                replacement = (*self.right).leftmost();
                replacement_child = (*replacement).right;
                replacement_parent = (*replacement).parent;
                update_replacement_side = true;
            } else {
                /* Replace with in-order predecessor node */
                replacement = (*self.left).rightmost();
                replacement_child = (*replacement).left;
                replacement_parent = (*replacement).parent;
                update_replacement_side = false;
            }

            if replacement_child != ptr::null_mut() {
                retrace_from = replacement_child;
            } else {
                retrace_from = replacement;
            }
        } else if self.left != ptr::null_mut() {
            /* One child */
            two_children = false;
            replacement = self.left;
            retrace_from = replacement;
        } else if self.right != ptr::null_mut() {
            /* ditto */
            two_children = false;
            replacement = self.right;
            retrace_from = replacement;
        } else {
            /* No children */
            two_children = false;
            if self.parent == ptr::null_mut() {
                /* We're the only node in the tree */
                return (ptr::null_mut(), self.data.take().unwrap());
            }

            replacement = ptr::null_mut();
            retrace_from = self_ptr;
        }

        (*retrace_from).retrace_delete();

        if replacement_parent != ptr::null_mut() {
            if update_replacement_side {
                if replacement != self.right {
                    (*replacement_parent).left = replacement_child;
                }
            } else {
                if replacement != self.left {
                    (*replacement_parent).right = replacement_child;
                }
            }

            /* Move replacement's child (if any) into replacement's old position */
            if replacement_parent != self_ptr && replacement_child != ptr::null_mut() {
                (*replacement_child).parent = replacement_parent;
            }
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

        assert_ne!(retrace_from, ptr::null_mut());
        self.left = ptr::null_mut();
        self.right = ptr::null_mut();

        if self.parent != ptr::null_mut() {
            if (*self.parent).left == self_ptr {
                (*self.parent).left = replacement;
            } else {
                (*self.parent).right = replacement;
            }
        }

        let new_root = (*retrace_from).recurse_to_root();
        self.parent = ptr::null_mut();

        if two_children {
            /* retrace_delete won't fix the height of the replacement node,
             * so make sure to do that manually. */

            let left_height: i64;
            let right_height: i64;

            let l = (*replacement).left;
            let r = (*replacement).right;

            if l != ptr::null_mut() {
                left_height = (*l).height();
            } else {
                left_height = 0;
            }

            if r != ptr::null_mut() {
                right_height = (*r).height();
            } else {
                right_height = 0;
            }

            (*replacement).balance = (right_height - left_height) as i8;
        }

        (new_root, self.data.take().unwrap())
    }

    unsafe fn retrace_delete(&mut self) -> *mut AVLTreeNode<T, K> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTreeNode<T, K>;
        }

        if (*self.parent).right == (self as *mut AVLTreeNode<T, K>) {
            /* Right subtree has decreased in height */

            if (*self.parent).balance < 0 {
                /* Parent is left-heavy. */
                let sibling = (*self.parent).left;
                let prev_balance = (*sibling).balance;

                if prev_balance > 0 {
                    (*sibling).left_right_rotate();
                } else {
                    (*self.parent).right_rotate(true);
                }

                if prev_balance == 0 {
                    return self.recurse_to_root();
                }
            } else if (*self.parent).balance == 0 {
                /* Tree is still balanced. */
                (*self.parent).set_balance(-1);
                return self.recurse_to_root();
            } else {
                (*self.parent).set_balance(0);
                return (*self.parent).retrace_delete();
            }
        } else {
            /* Left subtree has decreased in height */
            if (*self.parent).balance > 0 {
                /* Parent is right-heavy. */
                let sibling = (*self.parent).right;
                let prev_balance = (*sibling).balance;

                if prev_balance < 0 {
                    (*sibling).right_left_rotate();
                } else {
                    (*self.parent).left_rotate(true);
                }

                if prev_balance == 0 {
                    return self.recurse_to_root();
                }
            } else if (*self.parent).balance == 0 {
                (*self.parent).set_balance(1);
                return self.recurse_to_root();
            } else {
                (*self.parent).set_balance(0);
                return (*self.parent).retrace_delete();
            }
        }

        return (*self.parent).retrace_delete();
    }

    /// Insert a new node into this tree.
    ///
    /// Returns a tuple consisting of:
    ///   - a pointer to the new root node, and
    ///   - a reference to the inserted element.
    fn insert(&mut self, key: K, data: T) -> (*mut AVLTreeNode<T, K>, &mut AVLTreeNode<T, K>) {
        let mut cur: *mut AVLTreeNode<T, K> = self as *mut AVLTreeNode<T, K>;
        let new_node: *mut AVLTreeNode<T, K>;
        let self_ptr = self as *mut AVLTreeNode<T, K>;

        assert_ne!(self.left, self_ptr);
        assert_ne!(self.right, self_ptr);
        assert_ne!(self.parent, self_ptr);

        unsafe {
            new_node = AVLTreeNode::<T, K>::new_alloc(key, data);
        }

        loop {
            unsafe {
                if (*new_node).key < (*cur).key {
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

            if new_parent != ptr::null_mut() {
                (*new_parent).verify_balance();
            }

            (new_parent, &mut *new_node)
        }
    }

    unsafe fn right_rotate(&mut self, update_balance: bool) -> *mut AVLTreeNode<T, K> {
        let pivot = self.left;

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

        if update_balance {
            if (*pivot).balance == 0 {
                self.set_balance(-1);
                (*pivot).set_balance(1);
            } else {
                self.set_balance(0);
                (*pivot).set_balance(0);
            }
        }

        pivot
    }

    unsafe fn left_rotate(&mut self, update_balance: bool) -> *mut AVLTreeNode<T, K> {
        let pivot = self.right;

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

        if update_balance {
            if (*pivot).balance == 0 {
                self.set_balance(1);
                (*pivot).set_balance(-1);
            } else {
                self.set_balance(0);
                (*pivot).set_balance(0);
            }
        }

        pivot
    }

    unsafe fn right_left_rotate(&mut self) {
        let parent = self.parent;
        let pivot = self.left;

        let pivot_balance = (*pivot).balance;

        self.right_rotate(false);
        (*parent).left_rotate(false);

        if pivot_balance > 0 {
            (*parent).set_balance(-1);
            self.set_balance(0);
        } else if pivot_balance == 0 {
            (*parent).set_balance(0);
            self.set_balance(0);
        } else {
            (*parent).set_balance(0);
            self.set_balance(1);
        }

        (*pivot).set_balance(0);
    }

    unsafe fn left_right_rotate(&mut self) {
        let parent = self.parent;
        let pivot = self.right;

        let pivot_balance = (*pivot).balance;

        self.left_rotate(false);
        (*parent).right_rotate(false);

        if pivot_balance > 0 {
            (*parent).set_balance(0);
            self.set_balance(-1);
        } else if pivot_balance == 0 {
            (*parent).set_balance(0);
            self.set_balance(0);
        } else {
            (*parent).set_balance(1);
            self.set_balance(0);
        }

        (*pivot).set_balance(0);
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

        if (*self.parent).right == (self as *mut AVLTreeNode<T, K>) {
            /* We are right-hand child: */

            if (*self.parent).balance > 0 {
                /* Tree is unbalanced at parent. */
                if self.balance < 0 {
                    /* Right-Left case. */
                    self.right_left_rotate();
                } else {
                    /* Right-Right case. */
                    (*self.parent).left_rotate(true);
                }

                self.verify_balance();
            } else if (*self.parent).balance < 0 {
                /* Tree is perfectly balanced-- don't need to do anything further! */
                (*self.parent).set_balance(0);
                self.verify_balance();
                return self.recurse_to_root();
            } else {
                (*self.parent).set_balance(1);
                /* Need to continue retracing. */
                self.verify_balance();
                return (*self.parent).retrace_insert();
            }
        } else {
            /* We are left-hand child: */
            if (*self.parent).balance < 0 {
                if self.balance > 0 {
                    /* Left-Right case. */
                    self.left_right_rotate();
                } else {
                    /* Left-Left case. */
                    (*self.parent).right_rotate(true);
                }

                self.verify_balance();
            } else if (*self.parent).balance > 0 {
                (*self.parent).set_balance(0);
                self.verify_balance();
                return self.recurse_to_root();
            } else {
                (*self.parent).set_balance(-1);
                self.verify_balance();
                return (*self.parent).retrace_insert();
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

    fn height(&self) -> i64 {
        unsafe {
            if self.left != ptr::null_mut() && self.right != ptr::null_mut() {
                let left = (*self.left).height();
                let right = (*self.right).height();
                if left > right {
                    return left + 1;
                } else {
                    return right + 1;
                }
            } else if self.left != ptr::null_mut() {
                return (*self.left).height() + 1;
            } else if self.right != ptr::null_mut() {
                return (*self.right).height() + 1;
            } else {
                return 1;
            }
        }
    }

    fn verify_balance(&self) {
        unsafe {
            let left_height: i64;
            let right_height: i64;

            if self.left != ptr::null_mut() {
                //print!("L");
                (*self.left).verify_balance();
                left_height = (*self.left).height();
            } else {
                left_height = 0;
            }

            if self.right != ptr::null_mut() {
                //print!("R");
                (*self.right).verify_balance();
                right_height = (*self.right).height();
            } else {
                right_height = 0;
            }

            //print!("S");
            let balance = right_height - left_height;
            assert_eq!(balance, self.balance as i64);
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
