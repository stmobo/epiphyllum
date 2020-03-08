use alloc::alloc::Layout;
use core::ops::{Deref, DerefMut};
use core::ptr;

#[derive(Debug)]
#[repr(transparent)]
pub struct AVLTree<T: Ord> {
    root: *mut AVLTreeNode<T>,
}

impl<T: Ord> AVLTree<T> {
    pub fn new() -> AVLTree<T> {
        AVLTree {
            root: ptr::null_mut(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.root == ptr::null_mut()
    }

    unsafe fn find_first_recursive<P, R>(cur: *mut AVLTreeNode<T>, mapper: &P) -> Option<R>
    where
        P: Fn(&T) -> Option<R>,
    {
        if cur == ptr::null_mut() {
            return None;
        }

        if let Some(result) = mapper((*cur).data.as_mut().unwrap()) {
            return Some(result);
        }

        if (*cur).left != ptr::null_mut() {
            if let Some(result) = AVLTree::<T>::find_first_recursive((*cur).left, mapper) {
                return Some(result);
            }
        }

        AVLTree::<T>::find_first_recursive((*cur).right, mapper)
    }

    pub fn find_first<P, R>(&self, mapper: P) -> Option<R>
    where
        P: Fn(&T) -> Option<R>,
    {
        unsafe { AVLTree::<T>::find_first_recursive(self.root, &mapper) }
    }

    pub fn delete<K, F>(&mut self, key: K, key_func: F) -> Option<T>
    where
        K: Ord,
        F: Fn(&T) -> K,
    {
        use alloc::alloc::dealloc;
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            if let Some(p) = (*self.root).search(key, key_func) {
                let (new_root, ret) = (*p).remove();
                self.root = new_root;

                let layout = Layout::new::<AVLTreeNode<T>>();
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
    pub fn search_interval<K, F>(&self, key: K, key_func: F) -> Option<&T>
    where
        K: Ord,
        F: Fn(&T) -> (K, K),
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe { (*self.root).search_interval(key, key_func).map(|r| &*r) }
    }

    /// Get a reference to a value within this tree.
    pub fn search<K, F>(&self, key: K, key_func: F) -> Option<&T>
    where
        K: Ord,
        F: Fn(&T) -> K,
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            (*self.root)
                .search(key, key_func)
                .map(|p| (*p).data.as_ref().unwrap())
        }
    }

    /// Look up a value by interval in this tree and get a mutable reference to it.
    pub fn search_interval_mut<K, F>(&mut self, key: K, key_func: F) -> Option<&mut T>
    where
        K: Ord,
        F: Fn(&T) -> (K, K),
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe { (*self.root).search_interval(key, key_func) }
    }

    /// Look up a value in this tree and get a mutable reference to it.
    pub fn search_mut<K, F>(&mut self, key: K, key_func: F) -> Option<&mut T>
    where
        K: Ord,
        F: Fn(&T) -> K,
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe {
            (*self.root)
                .search(key, key_func)
                .map(|p| (*p).data.as_mut().unwrap())
        }
    }

    /// Insert a new node into this tree.
    ///
    /// Returns a reference to the inserted element.
    pub fn insert(&mut self, data: T) -> &mut T {
        if self.root != ptr::null_mut() {
            let (new_root, elem) = unsafe { (*self.root).insert(data) };
            self.root = new_root;
            elem.data.as_mut().unwrap()
        } else {
            unsafe {
                self.root = AVLTreeNode::<T>::new_alloc(data);
                (*self.root).data.as_mut().unwrap()
            }
        }
    }
}

impl<T: Ord> Drop for AVLTree<T> {
    fn drop(&mut self) {
        use alloc::alloc::dealloc;

        let layout = Layout::new::<AVLTreeNode<T>>();
        unsafe {
            if self.root != ptr::null_mut() {
                ptr::drop_in_place(self.root);
                dealloc(self.root as *mut u8, layout);
            }
        }
    }
}

unsafe impl<T: Ord> Send for AVLTree<T> {}
unsafe impl<T: Ord> Sync for AVLTree<T> {}

#[derive(Debug)]
pub struct AVLTreeNode<T: Ord> {
    data: Option<T>,
    parent: *mut AVLTreeNode<T>,
    left: *mut AVLTreeNode<T>,
    right: *mut AVLTreeNode<T>,
    balance: i8,
}

impl<T: Ord> Deref for AVLTreeNode<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.data.as_ref().unwrap()
    }
}

impl<T: Ord> DerefMut for AVLTreeNode<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data.as_mut().unwrap()
    }
}

impl<T: Ord> AVLTreeNode<T> {
    unsafe fn new_alloc(data: T) -> *mut AVLTreeNode<T> {
        use alloc::alloc::alloc;

        let layout = Layout::new::<AVLTreeNode<T>>();
        let new_node = alloc(layout) as *mut AVLTreeNode<T>;
        ptr::write(
            new_node,
            AVLTreeNode {
                data: Some(data),
                parent: ptr::null_mut(),
                left: ptr::null_mut(),
                right: ptr::null_mut(),
                balance: 0,
            },
        );

        new_node
    }

    fn search_interval<K, F>(&mut self, key: K, key_func: F) -> Option<&mut T>
    where
        K: Ord,
        F: Fn(&T) -> (K, K),
    {
        let mut cur: *mut AVLTreeNode<T> = self as *mut AVLTreeNode<T>;

        loop {
            unsafe {
                let (key_ival_start, key_ival_end) = key_func((*cur).data.as_ref().unwrap());

                if key >= key_ival_start && key < key_ival_end {
                    return Some((*cur).data.as_mut().unwrap());
                }

                if key < key_ival_start {
                    if (*cur).left != ptr::null_mut() {
                        cur = (*cur).left;
                    } else {
                        return None;
                    }
                } else {
                    if (*cur).right != ptr::null_mut() {
                        cur = (*cur).right;
                    } else {
                        return None;
                    }
                }
            }
        }
    }

    fn search<K, F>(&mut self, key: K, key_func: F) -> Option<*mut AVLTreeNode<T>>
    where
        K: Ord,
        F: Fn(&T) -> K,
    {
        let mut cur: *mut AVLTreeNode<T> = self as *mut AVLTreeNode<T>;

        loop {
            unsafe {
                let cur_key = key_func((*cur).data.as_ref().unwrap());

                if key == cur_key {
                    return Some(&mut *cur);
                }

                if key < cur_key {
                    if (*cur).left != ptr::null_mut() {
                        cur = (*cur).left;
                    } else {
                        return None;
                    }
                } else {
                    if (*cur).right != ptr::null_mut() {
                        cur = (*cur).right;
                    } else {
                        return None;
                    }
                }
            }
        }
    }

    unsafe fn leftmost(&mut self) -> *mut AVLTreeNode<T> {
        if self.left == ptr::null_mut() {
            return self as *mut AVLTreeNode<T>;
        } else {
            return (*self.left).leftmost();
        }
    }

    unsafe fn rightmost(&mut self) -> *mut AVLTreeNode<T> {
        if self.right == ptr::null_mut() {
            return self as *mut AVLTreeNode<T>;
        } else {
            return (*self.right).rightmost();
        }
    }

    /// Remove this node from the tree.
    unsafe fn remove(&mut self) -> (*mut AVLTreeNode<T>, T) {
        let self_ptr = self as *mut AVLTreeNode<T>;

        let replacement: *mut AVLTreeNode<T>;
        let retrace_from: *mut AVLTreeNode<T>;

        if self.left != ptr::null_mut() && self.right != ptr::null_mut() {
            /* Two children */
            let replacement_child: *mut AVLTreeNode<T>;
            let replacement_parent: *mut AVLTreeNode<T>;

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
            retrace_from = replacement;
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

    unsafe fn retrace_delete(&mut self) -> *mut AVLTreeNode<T> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTreeNode<T>;
        }

        let prev_parent = self.parent;
        if (*self.parent).right == (self as *mut AVLTreeNode<T>) {
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
    fn insert(&mut self, data: T) -> (*mut AVLTreeNode<T>, &mut AVLTreeNode<T>) {
        let mut cur: *mut AVLTreeNode<T> = self as *mut AVLTreeNode<T>;
        let new_node: *mut AVLTreeNode<T>;

        unsafe {
            new_node = AVLTreeNode::<T>::new_alloc(data);
        }

        loop {
            unsafe {
                let r1 = (*new_node).data.as_ref().unwrap();
                let r2 = (*cur).data.as_ref().unwrap();

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

    unsafe fn right_rotate(&mut self) -> *mut AVLTreeNode<T> {
        let pivot = self.left;

        if pivot != ptr::null_mut() {
            self.left = (*pivot).right;
            (*pivot).right = self as *mut AVLTreeNode<T>;

            if self.left != ptr::null_mut() {
                (*self.left).parent = self as *mut AVLTreeNode<T>;
            }

            let prev_parent = self.parent;
            if prev_parent != ptr::null_mut() {
                if (*prev_parent).left == (self as *mut AVLTreeNode<T>) {
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

    unsafe fn left_rotate(&mut self) -> *mut AVLTreeNode<T> {
        let pivot = self.right;

        if pivot != ptr::null_mut() {
            self.right = (*pivot).left;
            (*pivot).left = self as *mut AVLTreeNode<T>;

            if self.right != ptr::null_mut() {
                (*self.right).parent = self as *mut AVLTreeNode<T>;
            }

            let prev_parent = self.parent;
            if prev_parent != ptr::null_mut() {
                if (*prev_parent).left == (self as *mut AVLTreeNode<T>) {
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

    fn recurse_to_root(&mut self) -> *mut AVLTreeNode<T> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTreeNode<T>;
        } else {
            unsafe { (*self.parent).recurse_to_root() }
        }
    }

    /// Retracing loop after subtree height increases.
    ///
    /// Returns the new overall root of the tree.
    unsafe fn retrace_insert(&mut self) -> *mut AVLTreeNode<T> {
        if self.parent == ptr::null_mut() {
            return self as *mut AVLTreeNode<T>;
        }

        let prev_parent = self.parent;
        if (*self.parent).right == (self as *mut AVLTreeNode<T>) {
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
}

impl<T: Ord> Drop for AVLTreeNode<T> {
    fn drop(&mut self) {
        use alloc::alloc::dealloc;

        let layout = Layout::new::<AVLTreeNode<T>>();
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
