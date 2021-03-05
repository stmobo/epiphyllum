extern crate hashbrown;

pub mod avl_tree;
pub mod bip_buffer;
pub mod bitmask;
pub mod handle_list;
pub mod node_arena;
pub mod mpsc_channel;

pub use avl_tree::AVLTree;
pub use epiphyllum_structures::RBTree;
pub use bip_buffer::{BipBuffer, BipReader, BipWriter};
pub use bitmask::Bitmask64;
pub use handle_list::HandleList;
pub use hashbrown::{HashMap, HashSet};
pub use epiphyllum_structures::{Queue, QueueReader, QueueWriter, queue};
pub use mpsc_channel::{Channel, Receiver, Sender, channel};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rng::MersenneTwister64;
    use crate::test::TEST_SEED;

    use kernel_test_macro::kernel_test;

    // The main purpose of this test is to check for any weird interactions
    // with other parts of the kernel (for example, the memory allocation system)
    // that might cause hashbrown to fall over.
    #[kernel_test]
    fn test_hashmap() {
        let mut rng = MersenneTwister64::new(TEST_SEED);
        let mut map = HashMap::new();

        for _ in 0..10_000 {
            let k = rng.generate();
            let v = rng.generate();

            map.insert(k, v);
        }

        rng.seed(TEST_SEED);
        for _ in 0..10_000 {
            let k = rng.generate();
            let v = rng.generate();

            let retrieved = map.get(&k).unwrap();
            assert_eq!(*retrieved, v);
        }
    }
}
