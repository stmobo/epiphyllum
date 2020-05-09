use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Debug;
use core::iter::FusedIterator;
use core::mem::swap;
use core::ops::{Bound, RangeBounds};

use super::node_arena::ArenaList;

#[derive(Debug)]
pub struct Node<K: Ord, V> {
    parent: Option<usize>,
    left: Option<usize>,
    right: Option<usize>,
    key: K,
    val: V,
    balance: i8,
}

#[derive(Debug)]
pub struct AVLTree<K: Ord, V> {
    nodes: ArenaList<Node<K, V>>,
    root: usize,
}

impl<K: Ord, V> AVLTree<K, V> {
    pub fn new() -> AVLTree<K, V> {
        AVLTree {
            nodes: ArenaList::new(),
            root: 0,
        }
    }

    fn set_left_child(&mut self, parent: usize, child: Option<usize>) {
        let n = self
            .nodes
            .get_mut(parent)
            .expect("attempted to access invalid node");

        n.left = child;
        drop(n);
        if let Some(node) = child.and_then(|i| self.nodes.get_mut(i)) {
            node.parent = Some(parent);
        }
    }

    fn set_right_child(&mut self, parent: usize, child: Option<usize>) {
        let n = self
            .nodes
            .get_mut(parent)
            .expect("attempted to access invalid node");

        n.right = child;
        drop(n);
        if let Some(node) = child.and_then(|i| self.nodes.get_mut(i)) {
            node.parent = Some(parent);
        }
    }

    fn parent(&self, node: usize) -> Option<usize> {
        let n = self
            .nodes
            .get(node)
            .expect("attempted to access invalid node");

        n.parent
    }

    fn is_left_child(&self, parent: usize, child: usize) -> bool {
        let n = self
            .nodes
            .get(parent)
            .expect("attempted to access invalid node");

        return n.left.is_some() && n.left.unwrap() == child;
    }

    fn is_right_child(&self, parent: usize, child: usize) -> bool {
        let n = self
            .nodes
            .get(parent)
            .expect("attempted to access invalid node");

        return n.right.is_some() && n.right.unwrap() == child;
    }

    fn rotate(&mut self, pivot: usize) {
        let parent = self
            .parent(pivot)
            .expect("Attempted to rotate around root node");
        let gp = self.parent(parent);
        let parent_bal = self.nodes[parent].balance;
        let pivot_bal = self.nodes[pivot].balance;

        let internal_child: Option<usize>;
        let mut new_parent_bal: i8 = parent_bal;
        let mut new_pivot_bal: i8 = pivot_bal;
        if self.is_left_child(parent, pivot) {
            /* Right rotation */
            internal_child = self.nodes[pivot].right;
            self.set_left_child(parent, internal_child);
            self.set_right_child(pivot, Some(parent));

            new_parent_bal += 1;
            if pivot_bal < 0 {
                new_parent_bal -= pivot_bal;
            }

            new_pivot_bal += 1;
            if new_parent_bal > 0 {
                new_pivot_bal += new_parent_bal;
            }
        } else {
            /* Left Rotation */
            internal_child = self.nodes[pivot].left;
            self.set_right_child(parent, internal_child);
            self.set_left_child(pivot, Some(parent));

            new_parent_bal -= 1;
            if pivot_bal > 0 {
                new_parent_bal -= pivot_bal;
            }

            new_pivot_bal -= 1;
            if new_parent_bal < 0 {
                new_pivot_bal += new_parent_bal;
            }
        }

        self.nodes[pivot].balance = new_pivot_bal;
        self.nodes[parent].balance = new_parent_bal;

        if let Some(gp) = gp {
            if self.is_left_child(gp, parent) {
                self.set_left_child(gp, Some(pivot));
            } else {
                self.set_right_child(gp, Some(pivot));
            }
        } else {
            self.root = pivot;
            self.nodes[pivot].parent = None;
        }
    }

    fn rebalance(&mut self, node: usize) -> usize {
        let parent_bal = self.nodes[node].balance;
        let mut child: usize;

        if parent_bal < 0 {
            child = self.nodes[node].left.expect("invalid balance");
        } else {
            child = self.nodes[node].right.expect("invalid balance");
        }

        let child_bal = self.nodes[child].balance;
        if (parent_bal < 0) && (child_bal > 0) {
            child = self.nodes[child].right.expect("invalid balance");
            self.rotate(child);
        } else if (parent_bal > 0) && (child_bal < 0) {
            child = self.nodes[child].left.expect("invalid balance");
            self.rotate(child);
        }

        self.rotate(child);
        return child;
    }

    fn retrace_insert(&mut self, mut cur_node: usize) {
        let mut parent = self.parent(cur_node);

        while parent.is_some() {
            let parent_idx = parent.unwrap();
            let old_bal = self.nodes[parent_idx].balance;

            if self.is_left_child(parent_idx, cur_node) {
                self.nodes[parent_idx].balance -= 1;

                if old_bal < 0 {
                    self.rebalance(parent_idx);
                    break;
                } else if old_bal > 0 {
                    break;
                }
            } else {
                self.nodes[parent_idx].balance += 1;

                if old_bal > 0 {
                    self.rebalance(parent_idx);
                    break;
                } else if old_bal < 0 {
                    break;
                }
            }

            cur_node = parent_idx;
            parent = self.parent(parent_idx);
        }
    }

    pub fn insert(&mut self, key: K, val: V) -> Result<(), &V> {
        let node_idx = self.nodes.len();
        self.nodes.push(Node {
            parent: None,
            left: None,
            right: None,
            key,
            val: val,
            balance: 0,
        });

        if self.nodes.len() == 1 {
            self.root = 0;
            return Ok(());
        }

        let insert_key = &self.nodes[node_idx].key;
        let mut cur = self.root;

        loop {
            match insert_key.cmp(&self.nodes[cur].key) {
                Ordering::Equal => return Err(&self.nodes[cur].val),
                Ordering::Less => match self.nodes[cur].left {
                    Some(child) => cur = child,
                    None => {
                        self.set_left_child(cur, Some(node_idx));
                        break;
                    }
                },
                Ordering::Greater => match self.nodes[cur].right {
                    Some(child) => cur = child,
                    None => {
                        self.set_right_child(cur, Some(node_idx));
                        break;
                    }
                },
            }
        }

        self.retrace_insert(node_idx);
        Ok(())
    }

    fn find_helper<Q>(&self, key: &Q, cur: usize) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let next = match key.cmp(self.nodes[cur].key.borrow()) {
            Ordering::Equal => return Some(cur),
            Ordering::Less => self.nodes[cur].left?,
            Ordering::Greater => self.nodes[cur].right?,
        };

        self.find_helper(key, next)
    }

    pub fn validate(&self) {
        for idx in 0..self.nodes.len() {
            let node = &self.nodes[idx];

            if let Some(p) = node.parent {
                let parent = &self.nodes[p];

                if self.is_left_child(p, idx) {
                    assert!(node.key.lt(&parent.key));
                } else if self.is_right_child(p, idx) {
                    assert!(node.key.gt(&parent.key));
                } else {
                    panic!("broken parent/child link between nodes {} and {}", p, idx);
                }
            }
        }
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if self.nodes.len() == 0 {
            return None;
        }

        let idx = self.find_helper(key, self.root)?;
        Some(&self.nodes[idx].val)
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if self.nodes.len() == 0 {
            return None;
        }

        let idx = self.find_helper(key, self.root)?;
        Some(&mut self.nodes[idx].val)
    }

    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if self.nodes.len() == 0 {
            return false;
        }

        self.find_helper(key, self.root).is_some()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    fn delete_entry(&mut self, idx: usize) -> Node<K, V> {
        let removed = self.nodes.swap_remove(idx);
        if self.nodes.len() == 0 {
            return removed;
        }

        /* Fix links on parent. Removed node should not have any children. */
        if let Some(mut parent) = removed.parent {
            if parent == self.nodes.len() {
                parent = idx;
            }

            if self.is_left_child(parent, idx) {
                self.nodes[parent].left = None;
            } else {
                self.nodes[parent].right = None;
            }
        }

        if idx < self.nodes.len() {
            /* Fix links on swapped-in node's parent */
            let prev_idx = self.nodes.len();
            if let Some(parent) = self.nodes[idx].parent {
                /* Fix child links on parent */
                if self.is_left_child(parent, prev_idx) {
                    self.nodes[parent].left = Some(idx);
                } else {
                    self.nodes[parent].right = Some(idx);
                }
            } else {
                /* swapped-in node was root */
                self.root = idx;
            }

            /* Fix links on swapped-in node's children */
            if let Some(child) = self.nodes[idx].left {
                self.nodes[child].parent = Some(idx);
            }

            if let Some(child) = self.nodes[idx].right {
                self.nodes[child].parent = Some(idx);
            }
        }

        removed
    }

    fn retrace_remove(&mut self, mut cur_node: usize) {
        let mut parent = self.parent(cur_node);

        while parent.is_some() {
            let parent_idx = parent.unwrap();
            let old_bal = self.nodes[parent_idx].balance;

            if self.is_left_child(parent_idx, cur_node) {
                self.nodes[parent_idx].balance += 1;
                if old_bal > 0 {
                    let sibling = self.nodes[parent_idx].right.unwrap();
                    let sibling_bal = self.nodes[sibling].balance;

                    self.rebalance(parent_idx);
                    if sibling_bal == 0 {
                        break;
                    }
                }
            } else {
                self.nodes[parent_idx].balance -= 1;
                if old_bal < 0 {
                    let sibling = self.nodes[parent_idx].left.unwrap();
                    let sibling_bal = self.nodes[sibling].balance;

                    self.rebalance(parent_idx);
                    if sibling_bal == 0 {
                        break;
                    }
                }
            }

            if old_bal == 0 {
                break;
            }

            cur_node = parent_idx;
            parent = self.parent(parent_idx);
        }
    }

    fn leftmost(&self, cur: usize) -> usize {
        match self.nodes[cur].left {
            Some(idx) => self.leftmost(idx),
            None => cur,
        }
    }

    fn rightmost(&self, cur: usize) -> usize {
        match self.nodes[cur].right {
            Some(idx) => self.rightmost(idx),
            None => cur,
        }
    }

    fn swap_node_data(&mut self, a: usize, b: usize) {
        let p1 = self.nodes.element_pointer(a);
        let p2 = self.nodes.element_pointer(b);

        unsafe {
            swap(&mut (*p1).key, &mut (*p2).key);
            swap(&mut (*p1).val, &mut (*p2).val);
        }
    }

    fn remove_internal(&mut self, idx: usize) -> Node<K, V> {
        let left = self.nodes[idx].left;
        let right = self.nodes[idx].right;

        if left.is_some() && right.is_some() {
            /* Replace with in-order successor and delete that node instead */
            let successor = self.leftmost(right.unwrap());
            self.swap_node_data(successor, idx);
            return self.remove_internal(successor);
        } else if left.is_some() {
            let child = left.unwrap();
            self.swap_node_data(child, idx);
            return self.remove_internal(child);
        } else if right.is_some() {
            let child = right.unwrap();
            self.swap_node_data(child, idx);
            return self.remove_internal(child);
        } else {
            self.retrace_remove(idx);
            return self.delete_entry(idx);
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if self.nodes.len() == 0 {
            return None;
        }

        let idx = self.find_helper(key, self.root)?;
        let removed = self.remove_internal(idx);
        Some(removed.val)
    }

    fn next_node(&self, cur: usize) -> Option<usize> {
        if self.nodes.len() == 0 {
            return None;
        }

        if let Some(idx) = self.nodes[cur].right {
            Some(self.leftmost(idx))
        } else {
            let mut idx = cur;
            while self.nodes[idx].parent.is_some() {
                let parent = self.nodes[idx].parent.unwrap();
                if self.is_left_child(parent, idx) {
                    return Some(parent);
                }

                idx = parent;
            }

            None
        }
    }

    fn prev_node(&self, cur: usize) -> Option<usize> {
        if self.nodes.len() == 0 {
            return None;
        }

        if let Some(idx) = self.nodes[cur].left {
            Some(self.rightmost(idx))
        } else {
            let mut idx = cur;
            while self.nodes[idx].parent.is_some() {
                let parent = self.nodes[idx].parent.unwrap();
                if self.is_right_child(parent, idx) {
                    return Some(parent);
                }

                idx = parent;
            }

            None
        }
    }

    pub fn iter(&self) -> TreeRange<'_, K, V> {
        let left: usize;
        let right: usize;
        if self.is_empty() {
            left = 0;
            right = 0;
        } else {
            left = self.leftmost(self.root);
            right = self.rightmost(self.root);
        }

        TreeRange {
            done: self.is_empty(),
            left,
            right,
            tree: self,
        }
    }

    pub fn iter_mut(&mut self) -> TreeRangeMut<'_, K, V> {
        let left: usize;
        let right: usize;
        if self.is_empty() {
            left = 0;
            right = 0;
        } else {
            left = self.leftmost(self.root);
            right = self.rightmost(self.root);
        }

        TreeRangeMut {
            done: self.is_empty(),
            left,
            right,
            tree: self,
        }
    }

    /// Finds the smallest key that is to the right of the bound.
    fn lower_bound_index<Q>(&self, cur: usize, bound: Bound<&Q>) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let cur_node = &self.nodes[cur];
        let cur_key: &Q = cur_node.key.borrow();

        match bound {
            Bound::Unbounded => match cur_node.left {
                Some(idx) => self.lower_bound_index(idx, bound),
                None => Some(cur),
            },
            Bound::Included(key) => match key.cmp(cur_key) {
                Ordering::Equal => Some(cur),
                Ordering::Less => match cur_node.left {
                    Some(idx) => self.lower_bound_index(idx, bound),
                    None => Some(cur),
                },
                Ordering::Greater => match cur_node.right {
                    Some(idx) => self.lower_bound_index(idx, bound),
                    None => self.next_node(cur),
                },
            },
            Bound::Excluded(key) => match key.cmp(cur_key) {
                Ordering::Less => match cur_node.left {
                    Some(idx) => self.lower_bound_index(idx, bound),
                    None => Some(cur),
                },
                Ordering::Greater | Ordering::Equal => match cur_node.right {
                    Some(idx) => self.lower_bound_index(idx, bound),
                    None => self.next_node(cur),
                },
            },
        }
    }

    /// Finds the largest key that is to the left of the given bound.
    fn upper_bound_index<Q>(&self, cur: usize, bound: Bound<&Q>) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let cur_node = &self.nodes[cur];
        let cur_key: &Q = cur_node.key.borrow();

        match bound {
            Bound::Unbounded => match cur_node.right {
                Some(idx) => self.upper_bound_index(idx, bound),
                None => Some(cur),
            },
            Bound::Included(key) => match key.cmp(cur_key) {
                Ordering::Equal => Some(cur),
                Ordering::Less => match cur_node.left {
                    Some(idx) => self.upper_bound_index(idx, bound),
                    None => self.prev_node(cur),
                },
                Ordering::Greater => match cur_node.right {
                    Some(idx) => self.upper_bound_index(idx, bound),
                    None => Some(cur),
                },
            },
            Bound::Excluded(key) => match key.cmp(cur_key) {
                Ordering::Less | Ordering::Equal => match cur_node.left {
                    Some(idx) => self.upper_bound_index(idx, bound),
                    None => self.prev_node(cur),
                },
                Ordering::Greater => match cur_node.right {
                    Some(idx) => self.upper_bound_index(idx, bound),
                    None => Some(cur),
                },
            },
        }
    }

    pub fn lower_bound<Q>(&self, bound: Bound<&Q>) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if !self.is_empty() {
            if let Some(idx) = self.lower_bound_index(self.root, bound) {
                let cur_node = &self.nodes[idx];
                return Some((&cur_node.key, &cur_node.val));
            }
        }

        None
    }

    pub fn lower_bound_mut<Q>(&mut self, bound: Bound<&Q>) -> Option<(&K, &mut V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if !self.is_empty() {
            if let Some(idx) = self.lower_bound_index(self.root, bound) {
                let r = &mut self.nodes[idx];
                return Some((&r.key, &mut r.val));
            }
        }

        None
    }

    pub fn upper_bound<Q>(&self, bound: Bound<&Q>) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if !self.is_empty() {
            if let Some(idx) = self.upper_bound_index(self.root, bound) {
                let cur_node = &self.nodes[idx];
                return Some((&cur_node.key, &cur_node.val));
            }
        }

        None
    }

    pub fn upper_bound_mut<Q>(&mut self, bound: Bound<&Q>) -> Option<(&K, &mut V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if !self.is_empty() {
            if let Some(idx) = self.upper_bound_index(self.root, bound) {
                let r = &mut self.nodes[idx];
                return Some((&r.key, &mut r.val));
            }
        }

        None
    }

    pub fn range<Q, R>(&self, range: R) -> TreeRange<'_, K, V>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let start = range.start_bound();
        let end = range.end_bound();

        let start_idx = self.lower_bound_index(self.root, start);
        if start_idx.is_none() {
            return TreeRange::empty(self);
        }
        let start_idx = start_idx.unwrap();

        let end_idx = self.upper_bound_index(self.root, end);
        if end_idx.is_none() {
            return TreeRange::empty(self);
        }
        let end_idx = end_idx.unwrap();

        let lower_key = &self.nodes[start_idx].key;
        let upper_key = &self.nodes[end_idx].key;

        if lower_key.gt(upper_key) {
            return TreeRange::empty(self);
        }

        TreeRange::new(self, start_idx, end_idx)
    }

    pub fn range_mut<Q, R>(&mut self, range: R) -> TreeRangeMut<'_, K, V>
    where
        K: Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let start = range.start_bound();
        let end = range.end_bound();

        let start_idx = self.lower_bound_index(self.root, start);
        if start_idx.is_none() {
            return TreeRangeMut::empty(self);
        }
        let start_idx = start_idx.unwrap();

        let end_idx = self.upper_bound_index(self.root, end);
        if end_idx.is_none() {
            return TreeRangeMut::empty(self);
        }
        let end_idx = end_idx.unwrap();

        let lower_key = &self.nodes[start_idx].key;
        let upper_key = &self.nodes[end_idx].key;

        if lower_key.gt(upper_key) {
            return TreeRangeMut::empty(self);
        }

        TreeRangeMut::new(self, start_idx, end_idx)
    }
}

impl<K: Ord + Debug, V> AVLTree<K, V> {
    #[allow(dead_code)]
    fn print_recursive<F>(&self, fmt: &F, level: usize, node: usize)
    where
        F: Fn(&K) -> alloc_crate::string::String,
    {
        if let Some(idx) = self.nodes[node].right {
            self.print_recursive(fmt, level + 1, idx);
        }

        for _ in 0..level {
            print!("       ");
        }

        println!(
            "{} ({})",
            fmt(&self.nodes[node].key),
            self.nodes[node].balance
        );

        if let Some(idx) = self.nodes[node].left {
            self.print_recursive(fmt, level + 1, idx);
        }
    }

    #[allow(dead_code)]
    pub fn print<F>(&self, fmt: F)
    where
        F: Fn(&K) -> alloc_crate::string::String,
    {
        println!("");
        return self.print_recursive(&fmt, 0, self.root);
    }
}

pub struct TreeRange<'a, K: Ord + 'a, V: 'a> {
    tree: &'a AVLTree<K, V>,
    left: usize,
    right: usize,
    done: bool,
}

impl<'a, K: Ord + 'a, V: 'a> TreeRange<'a, K, V> {
    fn empty(tree: &'a AVLTree<K, V>) -> TreeRange<'a, K, V> {
        TreeRange {
            tree,
            left: 0,
            right: 0,
            done: true,
        }
    }

    fn new(tree: &'a AVLTree<K, V>, left: usize, right: usize) -> TreeRange<'a, K, V> {
        TreeRange {
            tree,
            left,
            right,
            done: tree.is_empty(),
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for TreeRange<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let cur_idx = self.left;
        let cur_node = &self.tree.nodes[cur_idx];

        if cur_idx != self.right {
            self.left = self.tree.next_node(self.left).unwrap();
        } else {
            self.done = true;
        }

        Some((&cur_node.key, &cur_node.val))
    }
}

impl<'a, K: Ord + 'a, V: 'a> DoubleEndedIterator for TreeRange<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let cur_idx = self.right;
        let cur_node = &self.tree.nodes[cur_idx];
        if cur_idx != self.left {
            self.right = self.tree.prev_node(self.right).unwrap();
        } else {
            self.done = true;
        }

        Some((&cur_node.key, &cur_node.val))
    }
}

impl<'a, K: Ord + 'a, V: 'a> FusedIterator for TreeRange<'a, K, V> {}

pub struct TreeRangeMut<'a, K: Ord + 'a, V: 'a> {
    tree: &'a mut AVLTree<K, V>,
    left: usize,
    right: usize,
    done: bool,
}

impl<'a, K: Ord + 'a, V: 'a> TreeRangeMut<'a, K, V> {
    fn empty(tree: &'a mut AVLTree<K, V>) -> TreeRangeMut<'a, K, V> {
        TreeRangeMut {
            tree,
            left: 0,
            right: 0,
            done: true,
        }
    }

    fn new(tree: &'a mut AVLTree<K, V>, left: usize, right: usize) -> TreeRangeMut<'a, K, V> {
        TreeRangeMut {
            done: tree.is_empty(),
            tree,
            left,
            right,
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for TreeRangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let cur_idx = self.left;
        if cur_idx != self.right {
            self.left = self.tree.next_node(self.left).unwrap();
        } else {
            self.done = true;
        }

        /* Use unsafe code to get the proper lifetime for the borrows.
         * This should be safe: since we're stepping through each node in-order
         * one by one and stopping when both ends of the iterator cross, we
         * shouldn't return any aliasing mutable references.
         *
         * The borrow checker also will prevent additional mutable borrows of
         * the original Tree while any refs returned here are alive.
         */
        let cur_node: *mut Node<K, V> = &mut self.tree.nodes[cur_idx];
        unsafe {
            let k: &'a K = &(*cur_node).key;
            let v: &'a mut V = &mut (*cur_node).val;

            Some((k, v))
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> DoubleEndedIterator for TreeRangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let cur_idx = self.right;
        if cur_idx != self.left {
            self.right = self.tree.prev_node(self.right).unwrap();
        } else {
            self.done = true;
        }

        /*
         * See above regarding safety.
         */
        let cur_node: *mut Node<K, V> = &mut self.tree.nodes[cur_idx];
        unsafe {
            let k: &'a K = &(*cur_node).key;
            let v: &'a mut V = &mut (*cur_node).val;

            Some((k, v))
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> FusedIterator for TreeRangeMut<'a, K, V> {}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_link<K, V>(tree: &AVLTree<K, V>, parent: usize, child: Option<usize>, left: bool)
    where
        K: Ord,
    {
        if left {
            assert_eq!(
                tree.nodes[parent].left, child,
                "invalid left link for node {}",
                parent
            );
        } else {
            assert_eq!(
                tree.nodes[parent].right, child,
                "invalid right link for node {}",
                parent
            );
        }

        if let Some(child) = child {
            assert_eq!(
                tree.nodes[child].parent,
                Some(parent),
                "invalid parent link for node {}",
                child
            );
        }
    }

    #[allow(dead_code)]
    fn print_recursive(tree: &AVLTree<i32, i32>, level: usize, node: usize) {
        if let Some(idx) = tree.nodes[node].right {
            print_recursive(tree, level + 1, idx);
        }

        for _ in 0..level {
            print!("       ");
        }

        println!("{:?} ({})", tree.nodes[node].key, tree.nodes[node].balance);

        if let Some(idx) = tree.nodes[node].left {
            print_recursive(tree, level + 1, idx);
        }
    }

    #[test]
    fn single_insert() {
        let mut tree = AVLTree::new();
        tree.insert(5, 7).unwrap();

        assert_eq!(tree.nodes.len(), 1, "incorrect node count");
        assert_eq!(tree.root, 0, "invalid root index");
        assert_eq!(tree.nodes[0].key, 5, "incorrect root key");
        assert_eq!(tree.nodes[0].val, 7, "incorrect root value");
    }

    #[test]
    fn multiple_insert() {
        let mut tree = AVLTree::new();
        tree.insert(5, 5).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(10, 10).unwrap();
        tree.insert(15, 15).unwrap();
        tree.insert(20, 20).unwrap();

        assert_eq!(tree.nodes.len(), 5, "incorrect node count");
        assert_eq!(tree.nodes[0].key, 5, "incorrect node 0 key");
        assert_eq!(tree.nodes[0].val, 5, "incorrect node 0 value");

        assert_eq!(tree.nodes[1].key, 1, "incorrect node 1 key");
        assert_eq!(tree.nodes[1].val, 1, "incorrect node 1 value");

        assert_eq!(tree.nodes[2].key, 10, "incorrect node 2 key");
        assert_eq!(tree.nodes[2].val, 10, "incorrect node 2 value");

        assert_eq!(tree.nodes[3].key, 15, "incorrect node 3 key");
        assert_eq!(tree.nodes[3].val, 15, "incorrect node 3 value");

        assert_eq!(tree.nodes[4].key, 20, "incorrect node 4 key");
        assert_eq!(tree.nodes[4].val, 20, "incorrect node 4 value");
    }

    #[test]
    fn balanced_insert() {
        let mut tree = AVLTree::new();
        tree.insert(5, 5).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(10, 10).unwrap();

        assert_eq!(tree.root, 0, "invalid root index");
        assert_link(&tree, 0, Some(1), true);
        assert_link(&tree, 0, Some(2), false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, None, false);

        assert_link(&tree, 2, None, true);
        assert_link(&tree, 2, None, false);
    }

    #[test]
    fn left_left_insert() {
        let mut tree = AVLTree::new();
        tree.insert(10, 10).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(1, 1).unwrap();

        assert_eq!(tree.root, 1, "invalid root index");
        assert_link(&tree, 1, Some(2), true);
        assert_link(&tree, 1, Some(0), false);

        assert_link(&tree, 0, None, true);
        assert_link(&tree, 0, None, false);

        assert_link(&tree, 2, None, true);
        assert_link(&tree, 2, None, false);
    }

    #[test]
    fn right_right_insert() {
        let mut tree = AVLTree::new();
        tree.insert(1, 1).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(10, 10).unwrap();

        assert_eq!(tree.root, 1, "invalid root index");
        assert_link(&tree, 1, Some(0), true);
        assert_link(&tree, 1, Some(2), false);

        assert_link(&tree, 0, None, true);
        assert_link(&tree, 0, None, false);

        assert_link(&tree, 2, None, true);
        assert_link(&tree, 2, None, false);
    }

    #[test]
    fn left_right_insert() {
        let mut tree = AVLTree::new();
        tree.insert(3, 3).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(2, 2).unwrap();

        assert_eq!(tree.root, 2, "invalid root index");
        assert_link(&tree, 2, Some(1), true);
        assert_link(&tree, 2, Some(0), false);

        assert_link(&tree, 0, None, true);
        assert_link(&tree, 0, None, false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, None, false);
    }

    #[test]
    fn right_left_insert() {
        let mut tree = AVLTree::new();
        tree.insert(1, 1).unwrap();
        tree.insert(3, 3).unwrap();
        tree.insert(2, 2).unwrap();

        assert_eq!(tree.root, 2, "invalid root index");
        assert_link(&tree, 2, Some(0), true);
        assert_link(&tree, 2, Some(1), false);

        assert_link(&tree, 0, None, true);
        assert_link(&tree, 0, None, false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, None, false);
    }

    #[test]
    fn deep_insert() {
        let mut tree = AVLTree::new();
        tree.insert(2, 2).unwrap();
        tree.insert(6, 6).unwrap();
        tree.insert(3, 3).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(4, 4).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(0, 0).unwrap();

        assert_eq!(tree.root, 2, "invalid root index");

        assert_link(&tree, 2, Some(3), true);
        assert_link(&tree, 2, Some(5), false);

        assert_link(&tree, 3, Some(6), true);
        assert_link(&tree, 3, Some(0), false);

        assert_link(&tree, 6, None, true);
        assert_link(&tree, 6, None, false);

        assert_link(&tree, 0, None, true);
        assert_link(&tree, 0, None, false);

        assert_link(&tree, 5, Some(4), true);
        assert_link(&tree, 5, Some(1), false);

        assert_link(&tree, 4, None, true);
        assert_link(&tree, 4, None, false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, None, false);
    }

    #[test]
    fn leaf_delete() {
        let mut tree = AVLTree::new();
        tree.insert(5, 5).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(10, 10).unwrap();

        tree.remove(&10);

        assert_eq!(tree.nodes.len(), 2, "incorrect node count");
        assert_eq!(tree.nodes[0].key, 5, "incorrect node 0 key");
        assert_eq!(tree.nodes[0].val, 5, "incorrect node 0 value");

        assert_eq!(tree.nodes[1].key, 1, "incorrect node 1 key");
        assert_eq!(tree.nodes[1].val, 1, "incorrect node 1 value");

        assert_eq!(tree.root, 0, "invalid root index");
        assert_link(&tree, 0, Some(1), true);
        assert_link(&tree, 0, None, false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, None, false);
    }

    #[test]
    fn right_child_delete() {
        let mut tree = AVLTree::new();
        tree.insert(5, 5).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(10, 10).unwrap();
        tree.insert(15, 15).unwrap();

        tree.remove(&10);

        assert_eq!(tree.nodes.len(), 3, "incorrect node count");
        assert_eq!(tree.nodes[0].key, 5, "incorrect node 0 key");
        assert_eq!(tree.nodes[0].val, 5, "incorrect node 0 value");

        assert_eq!(tree.nodes[1].key, 1, "incorrect node 1 key");
        assert_eq!(tree.nodes[1].val, 1, "incorrect node 1 value");

        assert_eq!(tree.nodes[2].key, 15, "incorrect node 2 key");
        assert_eq!(tree.nodes[2].val, 15, "incorrect node 2 value");

        assert_eq!(tree.root, 0, "invalid root index");
        assert_link(&tree, 0, Some(1), true);
        assert_link(&tree, 0, Some(2), false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, None, false);

        assert_link(&tree, 2, None, true);
        assert_link(&tree, 2, None, false);
    }

    #[test]
    fn left_child_delete() {
        let mut tree = AVLTree::new();
        tree.insert(5, 5).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(10, 10).unwrap();
        tree.insert(-5, -5).unwrap();

        tree.remove(&1);

        assert_eq!(tree.nodes.len(), 3, "incorrect node count");
        assert_eq!(tree.nodes[0].key, 5, "incorrect node 0 key");
        assert_eq!(tree.nodes[0].val, 5, "incorrect node 0 value");

        assert_eq!(tree.nodes[1].key, -5, "incorrect node 1 key");
        assert_eq!(tree.nodes[1].val, -5, "incorrect node 1 value");

        assert_eq!(tree.nodes[2].key, 10, "incorrect node 2 key");
        assert_eq!(tree.nodes[2].val, 10, "incorrect node 2 value");

        assert_eq!(tree.root, 0, "invalid root index");
        assert_link(&tree, 0, Some(1), true);
        assert_link(&tree, 0, Some(2), false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, None, false);

        assert_link(&tree, 2, None, true);
        assert_link(&tree, 2, None, false);
    }

    #[test]
    fn multi_child_delete() {
        let mut tree = AVLTree::new();
        tree.insert(5, 5).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(10, 10).unwrap();
        tree.insert(7, 7).unwrap();
        tree.insert(3, 3).unwrap();
        tree.insert(15, 15).unwrap();
        tree.insert(8, 8).unwrap();

        tree.remove(&5);
        tree.remove(&10);

        assert_eq!(tree.nodes.len(), 5, "incorrect node count");
        assert_eq!(tree.nodes[0].key, 7, "incorrect node 0 key");
        assert_eq!(tree.nodes[0].val, 7, "incorrect node 0 value");

        assert_eq!(tree.nodes[1].key, 1, "incorrect node 1 key");
        assert_eq!(tree.nodes[1].val, 1, "incorrect node 1 value");

        assert_eq!(tree.nodes[2].key, 15, "incorrect node 2 key");
        assert_eq!(tree.nodes[2].val, 15, "incorrect node 2 value");

        assert_eq!(tree.nodes[3].key, 8, "incorrect node 3 key");
        assert_eq!(tree.nodes[3].val, 8, "incorrect node 3 value");

        assert_eq!(tree.nodes[4].key, 3, "incorrect node 4 key");
        assert_eq!(tree.nodes[4].val, 3, "incorrect node 4 value");

        assert_eq!(tree.root, 0, "invalid root index");
        assert_link(&tree, 0, Some(1), true);
        assert_link(&tree, 0, Some(2), false);

        assert_link(&tree, 1, None, true);
        assert_link(&tree, 1, Some(4), false);

        assert_link(&tree, 2, Some(3), true);
        assert_link(&tree, 2, None, false);

        assert_link(&tree, 3, None, true);
        assert_link(&tree, 3, None, false);

        assert_link(&tree, 4, None, true);
        assert_link(&tree, 4, None, false);
    }

    fn height<K: Ord, T>(tree: &AVLTree<K, T>, node: usize) -> isize {
        let left_height;
        let right_height;
        if let Some(i) = tree.nodes[node].left {
            left_height = height(tree, i);
        } else {
            left_height = 0;
        }

        if let Some(i) = tree.nodes[node].right {
            right_height = height(tree, i);
        } else {
            right_height = 0;
        }

        if left_height > right_height {
            return 1 + left_height;
        } else {
            return 1 + right_height;
        }
    }

    fn validate_balance<K: Ord, T>(tree: &AVLTree<K, T>, node: usize) {
        let left_height;
        let right_height;
        if let Some(i) = tree.nodes[node].left {
            left_height = height(tree, i);
        } else {
            left_height = 0;
        }

        if let Some(i) = tree.nodes[node].right {
            right_height = height(tree, i);
        } else {
            right_height = 0;
        }

        let balance = right_height - left_height;
        assert_eq!(
            tree.nodes[node].balance as isize, balance,
            "incorrect balance for node {}",
            node
        );
    }

    fn recursive_validate<K: Ord, T>(tree: &AVLTree<K, T>, node: usize) {
        if let Some(idx) = tree.nodes[node].left {
            recursive_validate(tree, idx);
        }

        validate_balance(tree, node);

        if let Some(idx) = tree.nodes[node].right {
            recursive_validate(tree, idx);
        }
    }

    #[test]
    fn large_avl_validate() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        for i in 0..50 {
            tree.insert(i, i).unwrap();
        }

        recursive_validate(&tree, tree.root);
    }

    #[test]
    fn test_get() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        for i in 0..50 {
            tree.insert(i, 2 * i).unwrap();
        }

        let val = tree.get(&25).expect("could not find value");
        assert_eq!(*val, 50, "got incorrect value from tree");
    }

    #[test]
    fn test_find_mut() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        for i in 0..50 {
            tree.insert(i, 2 * i).unwrap();
        }

        {
            let r = tree.get_mut(&33).expect("could not find value");
            *r = 0;
        }

        let val = tree.get(&33).expect("could not find value");
        assert_eq!(*val, 0, "got incorrect value from tree");
    }

    #[test]
    fn test_contains() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        for i in 0..50 {
            tree.insert(i, 2 * i).unwrap();
        }

        assert!(tree.contains(&12));
    }

    #[test]
    fn test_iter() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        tree.insert(0, 0).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(10, 10).unwrap();

        let v: Vec<(&i32, &i32)> = tree.iter().collect();

        assert_eq!(
            v.len(),
            3,
            "incorrect number of elements returned by iterator"
        );
        assert_eq!(*v[0].0, 0, "iterator key 1 incorrect");
        assert_eq!(*v[1].0, 5, "iterator key 2 incorrect");
        assert_eq!(*v[2].0, 10, "iterator key 3 incorrect");

        for (key, val) in v {
            let r = tree.get(key).expect("could not find iterated key");
            assert_eq!(*val, *r, "iterator and get() returned different values");
        }
    }

    #[test]
    fn test_iter_back() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        tree.insert(0, 0).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(10, 10).unwrap();

        let v: Vec<(&i32, &i32)> = tree.iter().rev().collect();

        assert_eq!(
            v.len(),
            3,
            "incorrect number of elements returned by iterator"
        );
        assert_eq!(*v[0].0, 10, "iterator key 1 incorrect");
        assert_eq!(*v[1].0, 5, "iterator key 2 incorrect");
        assert_eq!(*v[2].0, 0, "iterator key 3 incorrect");

        for (key, val) in v {
            let r = tree.get(key).expect("could not find iterated key");
            assert_eq!(*val, *r, "iterator and get() returned different values");
        }
    }

    #[test]
    fn test_iter_mut() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        tree.insert(0, 0).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(10, 10).unwrap();

        let mut v: Vec<(&i32, &mut i32)> = tree.iter_mut().collect();

        assert_eq!(
            v.len(),
            3,
            "incorrect number of elements returned by iterator"
        );
        assert_eq!(*v[0].0, 0, "iterator key 1 incorrect");
        assert_eq!(*v[1].0, 5, "iterator key 2 incorrect");
        assert_eq!(*v[2].0, 10, "iterator key 3 incorrect");

        *v[1].1 = 20;

        assert_eq!(
            *tree.get(&0).expect("could not find key 0"),
            0,
            "incorrect value for key 0"
        );
        assert_eq!(
            *tree.get(&5).expect("could not find key 5"),
            20,
            "incorrect value for key 5"
        );
        assert_eq!(
            *tree.get(&10).expect("could not find key 10"),
            10,
            "incorrect value for key 10"
        );
    }

    #[test]
    fn test_range() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        tree.insert(8, 8).unwrap();
        tree.insert(4, 4).unwrap();
        tree.insert(0, 0).unwrap();
        tree.insert(6, 6).unwrap();
        tree.insert(2, 2).unwrap();
        tree.insert(3, 3).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(7, 7).unwrap();
        tree.insert(9, 9).unwrap();

        let v: Vec<(&i32, &i32)> = tree.range(5..8).collect();
        assert_eq!(
            v.len(),
            3,
            "incorrect number of elements returned by iterator"
        );

        assert_eq!(*v[0].0, 5, "iterator key 1 incorrect");
        assert_eq!(*v[1].0, 6, "iterator key 2 incorrect");
        assert_eq!(*v[2].0, 7, "iterator key 3 incorrect");
    }

    #[test]
    fn test_invalid_range() {
        let mut tree: AVLTree<i32, i32> = AVLTree::new();
        tree.insert(8, 8).unwrap();
        tree.insert(4, 4).unwrap();
        tree.insert(0, 0).unwrap();
        tree.insert(6, 6).unwrap();
        tree.insert(2, 2).unwrap();
        tree.insert(3, 3).unwrap();
        tree.insert(1, 1).unwrap();
        tree.insert(5, 5).unwrap();
        tree.insert(7, 7).unwrap();
        tree.insert(9, 9).unwrap();

        let v: Vec<(&i32, &i32)> = tree.range(8..5).collect();
        assert_eq!(
            v.len(),
            0,
            "incorrect number of elements returned by iterator"
        );

        let v: Vec<(&i32, &i32)> = tree
            .range((Bound::Excluded(5), Bound::Excluded(5)))
            .collect();
        assert_eq!(
            v.len(),
            0,
            "incorrect number of elements returned by iterator"
        );
    }
}
