//! RNG utilities for testing.
use alloc_crate::boxed::Box;
use core::iter;
use core::mem::MaybeUninit;

// MT19937-64 constants
const R: u64 = 31;
const N_64: usize = 312;
const M_64: usize = 156;
const A_64: u64 = 0xB5026F5AA96619E9;
const U_64: u64 = 29;
const D_64: u64 = 0x5555555555555555;
const S_64: u64 = 17;
const B_64: u64 = 0x71D67FFFEDA60000;
const T_64: u64 = 37;
const C_64: u64 = 0xFFF7EEE000000000;
const L_64: u64 = 43;
const F_64: u64 = 6364136223846793005;
const LOWER_MASK: u64 = (1 << R) - 1;
const UPPER_MASK: u64 = !LOWER_MASK;

fn mt64_seed_values(seed: u64) -> impl Iterator<Item = u64> {
    iter::successors(Some((0, seed)), |&(i, v)| {
        Some((i + 1, F_64.wrapping_mul(v ^ (v >> 62)).wrapping_add(i + 1)))
    })
    .map(|t| t.1)
}

/// A 64-bit RNG that uses the Mersenne Twister algorithm.
pub struct MersenneTwister64 {
    mt: Box<[u64; N_64]>,
    index: usize,
}

impl MersenneTwister64 {
    /// Create a new RNG instance seeded with the given value.
    pub fn new(seed: u64) -> MersenneTwister64 {
        let mut mt = Box::new([MaybeUninit::<u64>::uninit(); N_64]);
        for (p, v) in mt.iter_mut().zip(mt64_seed_values(seed)) {
            unsafe {
                p.as_mut_ptr().write(v);
            }
        }

        let mt = unsafe { Box::from_raw(Box::into_raw(mt) as *mut [u64; N_64]) };
        MersenneTwister64 {
            index: mt.len(),
            mt,
        }
    }

    /// Re-initialize this RNG instance with the given seed.
    pub fn seed(&mut self, v: u64) {
        self.index = self.mt.len();
        for (p, v) in self.mt.iter_mut().zip(mt64_seed_values(v)) {
            *p = v;
        }
    }

    const fn twist_calc(mt: &[u64; N_64], i: usize, i2: usize) -> u64 {
        let x = (mt[i] & UPPER_MASK) | (mt[i + 1] & LOWER_MASK);
        mt[i2] ^ (x >> 1) ^ (A_64 * (x & 1))
    }

    // Generates the next values for the internal state.
    fn twist(&mut self) {
        let n = self.mt.len();
        for i in 0..(n - M_64) {
            self.mt[i] = Self::twist_calc(&self.mt, i, i + M_64);
        }

        for i in (n - M_64)..(n - 1) {
            self.mt[i] = Self::twist_calc(&self.mt, i, (i + M_64) - n);
        }

        let x = (self.mt[n - 1] & UPPER_MASK) | (self.mt[0] & LOWER_MASK);
        self.mt[n - 1] = self.mt[M_64 - 1] ^ (x >> 1) ^ (A_64 * (x & 1));
        self.index = 0;
    }

    /// Extract a pseudorandom number.
    pub fn generate(&mut self) -> u64 {
        if self.index >= self.mt.len() {
            self.twist();
        }

        let mut y = self.mt[self.index];
        y = y ^ ((y >> U_64) & D_64);
        y = y ^ ((y << S_64) & B_64);
        y = y ^ ((y << T_64) & C_64);
        y = y ^ (y >> L_64);

        self.index += 1;
        y
    }
}

impl Iterator for MersenneTwister64 {
    type Item = u64;

    fn next(&mut self) -> Option<u64> {
        Some(self.generate())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kernel_test_macro::kernel_test;

    #[kernel_test]
    fn test_rng() {
        let rng = MersenneTwister64::new(0x1234567887654321u64);
        for (v1, v2) in TEST_DATA.iter().zip(rng) {
            assert_eq!(*v1, v2);
        }
    }

    const TEST_DATA: [u64; 100] = [
        8582126092704055981,
        3457164283249173755,
        13739405504153195,
        5976700750132269349,
        9202233740427162441,
        6030661401690652345,
        12536042451692607026,
        15903657761848205050,
        10834260931505329724,
        11682301729489872455,
        125241118420953870,
        5485657407842997038,
        5898053603042644534,
        17730368526063982561,
        13714565005626718380,
        7513323929517503017,
        4478041482723196358,
        3663382034998002457,
        10832215158336365751,
        307739761565606931,
        9656384518059546485,
        14340692765884312740,
        7038572276594525203,
        13796626177728431999,
        14712670314930264783,
        6184697064257943806,
        14815026647369167363,
        7802180404655674391,
        5938736037433746580,
        16070657113966933131,
        7334454725625679826,
        5708669060202822448,
        11478172003374500620,
        635977116774343876,
        16674559116370280012,
        501496234383181513,
        7545614115588510623,
        1864533479550249566,
        419171896378572008,
        12665531238622492791,
        17746315850144541512,
        10514644269285169854,
        7089951463559797394,
        12877655825670525906,
        6976414277131072531,
        14948363306441962561,
        2161491907461612211,
        16840477603518544830,
        1339288518563885613,
        12748134559267251730,
        16603700289746775982,
        2421759153473156556,
        16844489469111234469,
        5951550920362483708,
        10543210470869034234,
        16139493874317725011,
        6203420166261378322,
        17219275273620613233,
        15437597750404589431,
        10658456252611119964,
        15656819279247131107,
        12462009054614014800,
        9464988213006978578,
        3671452191142738656,
        5002685078203210567,
        7885153913538148681,
        630569875751906036,
        3266521266355887864,
        2449345131035587865,
        4193555378794818482,
        3380400970123991744,
        2456552597474099560,
        3373615083210531793,
        17802299869409485973,
        13893636660407548681,
        14781429411929283697,
        17191523639865319060,
        14175683731401773051,
        2085065349691746444,
        9608539419844458132,
        12996098237125171127,
        15165380139083775037,
        8840548205888642139,
        4633965794375412964,
        11447375986163190513,
        14345335141065004279,
        10608233875851585140,
        17938065989404419758,
        12096678716357207994,
        12491743129834157147,
        7922942311839021346,
        1163607382721649535,
        5405876116987853717,
        17374312755626478227,
        4101165032049874328,
        6169886166474454620,
        17225018462111715271,
        17734229013886502574,
        6721319342232989888,
        10738101277225278975,
    ];
}
