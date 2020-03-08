use alloc::alloc::Layout;
use core::ops::{Deref, DerefMut};
use core::ptr;

#[derive(Debug)]
#[repr(transparent)]
pub struct AVLTree<T: PartialOrd> {
    root: *mut AVLTreeNode<T>,
}

impl<T: PartialOrd> AVLTree<T> {
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
        P: Fn(&mut T) -> Option<R>,
    {
        if cur == ptr::null_mut() {
            return None;
        }

        if let Some(result) = mapper(&mut (*cur).data) {
            return Some(result);
        }

        if (*cur).left != ptr::null_mut() {
            if let Some(result) = AVLTree::<T>::find_first_recursive((*cur).left, mapper) {
                return Some(result);
            }
        }

        AVLTree::<T>::find_first_recursive((*cur).right, mapper)
    }

    pub fn find_first<P, R>(&mut self, mapper: P) -> Option<R>
    where
        P: Fn(&mut T) -> Option<R>,
    {
        unsafe { AVLTree::<T>::find_first_recursive(self.root, &mapper) }
    }

    pub fn search_interval<K, F>(&mut self, key: K, key_func: F) -> Option<&mut T>
    where
        K: PartialOrd,
        F: Fn(&T) -> (K, K),
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe { (*self.root).search_interval(key, key_func) }
    }

    pub fn search<K, F>(&mut self, key: K, key_func: F) -> Option<&mut T>
    where
        K: PartialOrd,
        F: Fn(&T) -> K,
    {
        if self.root == ptr::null_mut() {
            return None;
        }

        unsafe { (*self.root).search(key, key_func) }
    }

    /// Insert a new node into this tree.
    ///
    /// Returns a reference to the inserted element.
    pub fn insert(&mut self, data: T) -> &mut T {
        if self.root != ptr::null_mut() {
            let (new_root, elem) = unsafe { (*self.root).insert(data) };
            self.root = new_root;
            &mut elem.data
        } else {
            unsafe {
                self.root = AVLTreeNode::<T>::new_alloc(data);
                &mut (*self.root).data
            }
        }
    }
}

impl<T: PartialOrd> Drop for AVLTree<T> {
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

#[derive(Debug, Clone)]
pub struct AVLTreeNode<T: PartialOrd> {
    data: T,
    parent: *mut AVLTreeNode<T>,
    left: *mut AVLTreeNode<T>,
    right: *mut AVLTreeNode<T>,
    balance: i8,
}

impl<T: PartialOrd> Deref for AVLTreeNode<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T: PartialOrd> DerefMut for AVLTreeNode<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<T: PartialOrd> AVLTreeNode<T> {
    unsafe fn new_alloc(data: T) -> *mut AVLTreeNode<T> {
        use alloc::alloc::alloc;

        let layout = Layout::new::<AVLTreeNode<T>>();
        let new_node = alloc(layout) as *mut AVLTreeNode<T>;
        ptr::write(
            new_node,
            AVLTreeNode {
                data,
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
        K: PartialOrd,
        F: Fn(&T) -> (K, K),
    {
        let mut cur: *mut AVLTreeNode<T> = self as *mut AVLTreeNode<T>;

        loop {
            unsafe {
                let (key_ival_start, key_ival_end) = key_func(&(*cur).data);

                if key >= key_ival_start && key < key_ival_end {
                    return Some(&mut (*cur).data);
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

    fn search<K, F>(&mut self, key: K, key_func: F) -> Option<&mut T>
    where
        K: PartialOrd,
        F: Fn(&T) -> K,
    {
        let mut cur: *mut AVLTreeNode<T> = self as *mut AVLTreeNode<T>;

        loop {
            unsafe {
                let cur_key = key_func(&(*cur).data);

                if key == cur_key {
                    return Some(&mut (*cur).data);
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
                if (*new_node).data < (*cur).data {
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
        }

        pivot
    }

    unsafe fn left_rotate(&mut self) -> *mut AVLTreeNode<T> {
        let pivot = self.right;

        if pivot != ptr::null_mut() {
            self.right = (*pivot).left;
            (*pivot).left = self as *mut AVLTreeNode<T>;

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
        if (*self.parent).right == (self as *mut AVLTreeNode<T>) {
            /* We are right-hand child: */

            if (*self.parent).balance > 0 {
                /* Tree is unbalanced at parent. */
                if self.balance >= 0 {
                    /* Right-Right case. */
                    (*self.parent).left_rotate();
                } else {
                    /* Right-Left case. */
                    let prev_parent = self.parent;
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
                    let prev_parent = self.parent;
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

impl<T: PartialOrd> Drop for AVLTreeNode<T> {
    fn drop(&mut self) {
        use alloc::alloc::dealloc;

        let layout = Layout::new::<AVLTreeNode<T>>();
        unsafe {
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
