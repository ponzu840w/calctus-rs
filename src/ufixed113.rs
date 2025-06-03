// ufixed113.rs

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UFixed113 {
    /// 下位 113 ビットのみを使う
    /// (1 << 113) - 1 でマスクして保持する
    val: u128,
}

impl UFixed113 {
    const BITS: u32 = 113;
    const MASK: u128 = (1u128 << Self::BITS) - 1;

    /// 0 を表す
    pub const ZERO: UFixed113 = UFixed113 { val: 0 };
    /// 1 を表す
    pub const ONE: UFixed113 = UFixed113 { val: 1 };

    /// self + other をして (結果, キャリー) を返す
    /// キャリーは 0 or 1 のどちらか
    pub fn add(&self, other: &UFixed113) -> (UFixed113, u32) {
        let sum = self.val + other.val;
        // 下位 113 ビットを取り出す
        let result = sum & Self::MASK;
        // キャリーは (sum >> 113) の下位ビット
        let carry = ((sum >> Self::BITS) & 1) as u32;
        (UFixed113 { val: result }, carry)
    }

    /// self - other をして (結果, borrow) を返す
    /// borrow はアンダーフローが起きたら 1、それ以外は 0
    pub fn sub(&self, other: &UFixed113) -> (UFixed113, u32) {
        // 自然な u128 の wrapping_sub を使い、下位 113 ビットにマスクすることで
        // アンダーフロー時は (x - y + 2^128) mod 2^113 が得られる
        let diff = self.val.wrapping_sub(other.val) & Self::MASK;
        // borrow は self.val < other.val で判断
        let borrow = if self.val < other.val { 1 } else { 0 };
        (UFixed113 { val: diff }, borrow)
    }

    /// 基本的な加減算の動作検証を行う (失敗すると panic)
    pub fn test() {
        // 1 + 1 = 0, carry = 1
        let (r1, c1) = UFixed113::ONE.add(&UFixed113::ONE);
        assert_eq!(r1, UFixed113::ZERO, "1 + 1 の結果が期待値と異なります");
        assert_eq!(c1, 1, "1 + 1 のキャリーが期待値と異なります");

        // 1 - 1 = 0, borrow = 0
        let (r2, b2) = UFixed113::ONE.sub(&UFixed113::ONE);
        assert_eq!(r2, UFixed113::ZERO, "1 - 1 の結果が期待値と異なります");
        assert_eq!(b2, 0, "1 - 1 の borrow が期待値と異なります");

        // 0 + 0 = 0, carry = 0
        let (r3, c3) = UFixed113::ZERO.add(&UFixed113::ZERO);
        assert_eq!(r3, UFixed113::ZERO, "0 + 0 の結果が期待値と異なります");
        assert_eq!(c3, 0, "0 + 0 の carry が期待値と異なります");

        // 0 - 1 → underflow, borrow = 1, 結果 = 2^113 - 1
        let (r4, b4) = UFixed113::ZERO.sub(&UFixed113::ONE);
        assert_eq!(b4, 1, "0 - 1 の borrow が期待値と異なります");

        // 2^113 - 1 を手動で作成
        let expected_max = UFixed113 { val: Self::MASK };
        assert_eq!(r4, expected_max, "0 - 1 の結果が期待値と異なります");
    }
}

// 大小比較のために Impl Ord / PartialOrd
impl PartialOrd for UFixed113 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UFixed113 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.val.cmp(&other.val)
    }
}
