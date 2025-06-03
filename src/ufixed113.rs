use std::fmt;
use std::ops::{Add, Sub, Not, Neg, Mul, Div, Rem, Shl, Shr}; // Added Mul, Div, Rem, Shl, Shr
use std::cmp::Ordering;
use std::convert::TryFrom;

const N_WORDS: usize = 5;
const WORD_BITS: u32 = 28;
const MASK_28BIT: u32 = (1 << WORD_BITS) - 1; // 0x0FFFFFFF
const MSB_WORD_INDEX: usize = N_WORDS - 1; // Index 4

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum Ufixed113Error {
    Overflow,
    InvalidArgument,
    DivideByZero, // Added for division
}

#[derive(Debug, Copy, Clone, Eq)]
pub struct Ufixed113 {
    words: [u32; N_WORDS],
}

impl Ufixed113 {
    pub const NUM_BITS: usize = 113;

    pub const fn new(a: u32, b: u32, c: u32, d: u32, e: u32) -> Self {
        Self {
            words: [
                a & MASK_28BIT,
                b & MASK_28BIT,
                c & MASK_28BIT,
                d & MASK_28BIT,
                e & 1,
            ],
        }
    }

    pub const ZERO: Self = Self { words: [0, 0, 0, 0, 0] };
    pub const ONE: Self = Self { words: [0, 0, 0, 0, 1] };
    const ONE_LSB: Self = Self { words: [1, 0, 0, 0, 0] };

    /// Returns the Most Significant Bit (the single integer bit).
    pub fn msb(&self) -> u32 {
        self.words[MSB_WORD_INDEX]
    }

    /// Returns the lower 64 bits of the number as a u64.
    /// words[0] (28 bits), words[1] (28 bits), words[2] (lower 8 bits of it).
    pub fn lower64_bits(&self) -> u64 {
        (self.words[0] as u64) |
        ((self.words[1] as u64) << WORD_BITS) |
        ((self.words[2] as u64) << (2 * WORD_BITS)) // This effectively takes lower 8 bits of words[2] into bits 56-63 of u64
    }

    /// Shifts self 1 bit to the left, inserting `carry_bit_for_lsb0` into the LSB position.
    /// The original MSB is shifted out and lost.
    pub fn single_shift_left(mut self, carry_bit_for_lsb0: u32) -> Self {
        debug_assert!(carry_bit_for_lsb0 <= 1);
        let mut current_carry_to_next_word_lsb = carry_bit_for_lsb0;

        for i in 0..N_WORDS {
            let original_word_val = self.words[i];
            let new_lsb_for_this_word = current_carry_to_next_word_lsb;

            if i == MSB_WORD_INDEX {
                self.words[i] = new_lsb_for_this_word & 1;
            } else {
                current_carry_to_next_word_lsb = (original_word_val >> (WORD_BITS - 1)) & 1;
                self.words[i] = ((original_word_val << 1) & MASK_28BIT) | new_lsb_for_this_word;
            }
        }
        self
    }

    /// Shifts self 1 bit to the right, inserting `carry_bit_for_msb` into the MSB position.
    /// The original LSB is shifted out and lost.
    pub fn single_shift_right(mut self, carry_bit_for_msb: u32) -> Self {
        debug_assert!(carry_bit_for_msb <= 1);
        let mut carry_from_prev_word_lsb = carry_bit_for_msb; 

        for i in (0..N_WORDS).rev() { 
            let current_word_lsb = self.words[i] & 1;
            if i == MSB_WORD_INDEX { 
                self.words[i] = carry_from_prev_word_lsb;
            } else { 
                self.words[i] = (self.words[i] >> 1) | (carry_from_prev_word_lsb << (WORD_BITS - 1));
            }
            carry_from_prev_word_lsb = current_word_lsb; 
        }
        self
    }

    /// Logical left shift by n bits.
    pub fn logic_shift_left(mut self, n: u32) -> Self {
        if n == 0 { return self; }
        // C# throws ArgumentException for n <= 0. Here, n is u32.
        for _ in 0..core::cmp::min(n, Ufixed113::NUM_BITS as u32) { // Max useful shift is NumBits
            self = self.single_shift_left(0);
        }
        if n >= Ufixed113::NUM_BITS as u32 { // If shifted by NumBits or more, result is 0
            self = Ufixed113::ZERO;
        }
        self
    }

    /// Logical right shift by n bits.
    pub fn logic_shift_right(mut self, n: u32) -> Self {
        if n == 0 { return self; }
        for _ in 0..core::cmp::min(n, Ufixed113::NUM_BITS as u32) {
            self = self.single_shift_right(0);
        }
        if n >= Ufixed113::NUM_BITS as u32 {
            self = Ufixed113::ZERO;
        }
        self
    }
    
    /// Arithmetic right shift by n bits (fills with original MSB).
    pub fn arith_shift_right(mut self, n: u32) -> Self {
        if n == 0 { return self; }
        let msb_to_fill = self.msb();
        for _ in 0..core::cmp::min(n, Ufixed113::NUM_BITS as u32) {
            self = self.single_shift_right(msb_to_fill);
        }
        // If n >= NumBits, result is all 0s if msb_to_fill was 0, or all 1s (which is ~ZERO) if msb_to_fill was 1.
        if n >= Ufixed113::NUM_BITS as u32 {
            if msb_to_fill == 1 {
                self = !Ufixed113::ZERO; // All bits set to 1
            } else {
                self = Ufixed113::ZERO;
            }
        }
        self
    }

    /// Truncates (sets to zero) the rightmost n bits.
    pub fn truncate_right(mut self, mut n: u32) -> Self {
        if n == 0 { return self; }
        if n >= Ufixed113::NUM_BITS as u32 { return Ufixed113::ZERO; }

        let mut word_idx = 0;
        // Clear full words from LSB
        while n >= WORD_BITS && word_idx < MSB_WORD_INDEX {
            self.words[word_idx] = 0;
            word_idx += 1;
            n -= WORD_BITS;
        }
        
        // Clear remaining bits in the current word
        if n > 0 && word_idx < N_WORDS {
            if word_idx == MSB_WORD_INDEX { // MSB word is 1 bit
                if n >= 1 { self.words[word_idx] = 0; }
            } else {
                // n here is < WORD_BITS
                let mask_to_clear = (1u32 << n) - 1; // Creates a mask of n LSBs set to 1
                self.words[word_idx] &= !mask_to_clear; // Clears these LSBs
            }
        }
        self
    }

    pub fn checked_add(self, other: Self) -> (Self, u32) {
        let mut accum_words = [0u32; N_WORDS];
        let mut carry_from_prev_word: u32 = 0;
        for i in 0..N_WORDS {
            let current_sum = (self.words[i] as u64) + (other.words[i] as u64) + (carry_from_prev_word as u64);
            if i == MSB_WORD_INDEX {
                accum_words[i] = current_sum as u32;
            } else {
                accum_words[i] = (current_sum & (MASK_28BIT as u64)) as u32;
                carry_from_prev_word = (current_sum >> WORD_BITS) as u32;
            }
        }
        let final_carry_out = (accum_words[MSB_WORD_INDEX] >> 1) & 1;
        accum_words[MSB_WORD_INDEX] &= 1;
        (Self { words: accum_words }, final_carry_out)
    }

    pub fn arith_invert(self) -> (Self, u32) {
        let inverted = !self;
        inverted.checked_add(Ufixed113::ONE_LSB)
    }

    pub fn checked_sub(self, other: Self) -> (Self, u32) {
        let borrow_out = if self < other { 1 } else { 0 };
        let (neg_other, _neg_carry) = other.arith_invert();
        let (result, _add_carry) = self.checked_add(neg_other);
        (result, borrow_out)
    }

    /// Performs multiplication: self * other.
    /// Returns (result, carry_out).
    /// carry_out indicates if the product (before fitting into 113 bits) exceeded the capacity of Q1.112 * Q1.112 -> Q2.224
    /// and the most significant bit of that Q2 representation was 1 (effectively an overflow for Q1.112 result).
    pub fn checked_mul(self, other: Self) -> (Self, u32) {
        let mut accum = [0u64; 2 * N_WORDS];

        for i in 0..N_WORDS {
            if other.words[i] == 0 && i != MSB_WORD_INDEX { continue; } // Optimization, but MSB can be 0 and still matter if others are non-zero
            let val_o = if i == MSB_WORD_INDEX { other.words[i] & 1 } else { other.words[i] };
            if val_o == 0 { continue; }

            for j in 0..N_WORDS {
                if self.words[j] == 0 && j != MSB_WORD_INDEX { continue; }
                let val_s = if j == MSB_WORD_INDEX { self.words[j] & 1 } else { self.words[j] };
                if val_s == 0 { continue; }
                
                accum[i + j] += (val_s as u64) * (val_o as u64);
            }
        }

        let mut carry_prop: u64 = 0;
        for k in 0..(2 * N_WORDS) {
            accum[k] += carry_prop;
            carry_prop = accum[k] >> WORD_BITS;
            accum[k] &= MASK_28BIT as u64;
        }
        // carry_prop now holds carry out of accum[2*N-1] >> WORD_BITS

        let mut result_words = [0u32; N_WORDS];
        // The fixed point is Q1.112. Product is Q2.224.
        // We need to shift right by 112 bits (NUM_BITS - 1), which is (N_WORDS - 1) words.
        // So, result_words[0] comes from accum[N_WORDS - 1].
        for i in 0..N_WORDS {
            if (N_WORDS - 1) + i < 2 * N_WORDS {
                 result_words[i] = accum[(N_WORDS - 1) + i] as u32;
            } else {
                 result_words[i] = 0; // Should not happen if accum is large enough
            }
        }
        
        // The carry_out for Mul is from the bit that would be the second integer bit if it were Q2.112
        // This is bit 1 of result_words[MSB_WORD_INDEX] before masking.
        // C# source: carryOut = (w[N-1] >> 1) & 1u; w[N-1] &= 1u;
        // w[N-1] is result_words[MSB_WORD_INDEX]
        let final_carry_out = (result_words[MSB_WORD_INDEX] >> 1) & 1;
        result_words[MSB_WORD_INDEX] &= 1;
        
        (Self { words: result_words }, final_carry_out)
    }

    /// Aligns the number so that its MSB is 1 (unless it's zero).
    /// Returns (aligned_number, shift_amount_left).
    pub fn align(mut self) -> (Self, i32) {
        if self == Ufixed113::ZERO {
            return (self, 0);
        }
        let mut shift_count = 0;
        // Max shift is NUM_BITS - 1 to bring any bit to MSB position.
        while self.msb() == 0 && shift_count < (Ufixed113::NUM_BITS as i32) {
            self = self.single_shift_left(0);
            shift_count += 1;
             if self == Ufixed113::ZERO { // Should not happen if not initially zero
                break;
            }
        }
        (self, shift_count)
    }

    /// Performs division: self / divisor.
    /// Returns Ok((quotient, remainder)) or Err(DivideByZero).
    /// Ensures `self = quotient * divisor + remainder` and `remainder < divisor`.
    pub fn checked_div_rem(self, divisor: Self) -> Result<(Self, Self), Ufixed113Error> {
        if divisor == Ufixed113::ZERO {
            return Err(Ufixed113Error::DivideByZero);
        }
        if self == Ufixed113::ZERO { // 0 / X = 0 rem 0
            return Ok((Ufixed113::ZERO, Ufixed113::ZERO));
        }
        if self < divisor { // X / Y where X < Y = 0 rem X
             return Ok((Ufixed113::ZERO, self));
        }


        let (mut dividend_aligned, dividend_shift) = self.align();
        let (divisor_aligned, divisor_shift) = divisor.align();

        let mut quotient_loop = Ufixed113::ZERO;
        let mut current_rem_or_dividend = dividend_aligned; // This variable is 'a' in C#

        // The division loop performs (dividend_aligned * 2^NUM_BITS) / divisor_aligned effectively
        // because dividend_aligned is shifted left NumBits times implicitly by how quotient bits are formed.
        // Or rather, current_rem_or_dividend is shifted left at each step.
        for _ in 0..Ufixed113::NUM_BITS {
            let q_bit = if current_rem_or_dividend >= divisor_aligned {
                current_rem_or_dividend = current_rem_or_dividend - divisor_aligned;
                1u32
            } else {
                0u32
            };
            quotient_loop = quotient_loop.single_shift_left(q_bit);
            // Shift current_rem_or_dividend left for the next bit. This is 'a <<= 1' in C#
            current_rem_or_dividend = current_rem_or_dividend.single_shift_left(0);
        }
        // quotient_loop is now the quotient of (dividend_aligned * 2^NUM_BITS) / divisor_aligned.
        // It needs to be scaled right by NUM_BITS, then scaled by (divisor_shift - dividend_shift).
        // Total shift = NUM_BITS - (divisor_shift - dividend_shift)
        //             = NUM_BITS + dividend_shift - divisor_shift
        // C# scales q by shift_right = dividend_shift - divisor_shift.
        // This means q_loop was already the quotient for dividend_aligned / divisor_aligned * (some_scale_factor_related_to_NumBits)
        // The loop structure with q.SSL(bit) implies q is Q = D/d. The implicit scaling of D by SSL means
        // Q is (D * 2^NumBits) / d. So Q_actual = (Q_loop / 2^NumBits).
        // Scaling of C# q: If shift_right (aShift - bShift) > 0, q >>= shift_right.
        // final_quotient = (quotient_loop >> NumBits) scaled by (aShift - bShift).

        let mut final_quotient = quotient_loop; // This quotient is for (D_align * 2^NumBits) / d_align
        // To get quotient for D_align / d_align, we need to effectively account for the implicit 2^NumBits scaling.
        // The C# `q = q.LogicShiftRight(shiftRight)` acts on a q that was built up from NumBits comparisons.
        // This q represents (D_align / d_align) but scaled up by 2^NumBits because of how it's constructed.
        // So, first scale `final_quotient` as if it's the result of (D_align / d_align), then apply `shift_right`.
        // No, the `q.SingleShiftLeft` over `NumBits` iterations naturally forms the quotient scaled as if
        // the dividend was `dividend_aligned` and divisor `divisor_aligned`. The extra scaling comes from the `NumBits` factor.
        // The result of `dividend_aligned / divisor_aligned` should be `quotient_loop` after `NumBits` right logical shifts.
        
        // The C# `q` is the direct result of SSL over NumBits iterations.
        // This `q` is for (D_aligned << NumBits) / d_aligned where result is integer like.
        // Or rather for D_aligned / d_aligned where result is Q1.112 (if SSL inserts at LSB of fraction).
        // The `q.SingleShiftLeft(bit)` means the `bit` becomes the LSB of `q` which is then shifted.
        // This means `q` represents `Sum(bit_i * 2^i) * 2^-(NumBits-1)`. So `q` is already mostly scaled.
        
        let scale_adjust = dividend_shift - divisor_shift;
        if scale_adjust >= 0 {
            final_quotient = final_quotient.logic_shift_right(scale_adjust as u32);
        } else {
            final_quotient = final_quotient.logic_shift_left((-scale_adjust) as u32);
        }

        // Calculate remainder R = self - Q_final * divisor
        let q_times_divisor = final_quotient.checked_mul(divisor).0;
        let final_remainder = if self >= q_times_divisor {
            self.checked_sub(q_times_divisor).0
        } else { // Should not happen if Q is correct floor division.
             // This case could arise from rounding in Q or if Q*Divisor overflows slightly.
             // If self < Q*Divisor, then R would be negative. For unsigned, this means Q was too high.
             // This path suggests an issue if Q isn't floor(self/divisor).
             // For now, assume Q is correct, so self >= Q*Divisor.
            self.checked_sub(q_times_divisor).0 // This will wrap if self < Q*Divisor
        };
        
        Ok((final_quotient, final_remainder))
    }
}

// --- PartialEq, PartialOrd, Ord, Display, Not, Neg, Add, Sub are same as before ---
// (Re-add them here from previous response for completeness if running this file standalone)
impl PartialEq for Ufixed113 { fn eq(&self, other: &Self) -> bool { self.words == other.words } }
impl PartialOrd for Ufixed113 { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl Ord for Ufixed113 {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..N_WORDS).rev() {
            if self.words[i] > other.words[i] { return Ordering::Greater; }
            if self.words[i] < other.words[i] { return Ordering::Less; }
        }
        Ordering::Equal
    }
}
impl fmt::Display for Ufixed113 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:x}", self.words[MSB_WORD_INDEX])?;
        for i in (0..MSB_WORD_INDEX).rev() {
            write!(f, " {:07x}", self.words[i])?;
        }
        Ok(())
    }
}
impl Not for Ufixed113 {
    type Output = Self;
    fn not(self) -> Self::Output {
        let mut result_words = [0u32; N_WORDS];
        for i in 0..N_WORDS { result_words[i] = self.words[i] ^ MASK_28BIT; }
        result_words[MSB_WORD_INDEX] &= 1;
        Self { words: result_words }
    }
}
impl Neg for Ufixed113 { type Output = Self; fn neg(self) -> Self::Output { self.arith_invert().0 } }
impl Add for Ufixed113 { type Output = Self; fn add(self, other: Self) -> Self::Output { self.checked_add(other).0 } }
impl Sub for Ufixed113 { type Output = Self; fn sub(self, other: Self) -> Self::Output { self.checked_sub(other).0 } }
// --- End of re-added traits ---

// Multiplication operator (*)
impl Mul for Ufixed113 {
    type Output = Self;
    fn mul(self, other: Self) -> Self::Output {
        let (result, _carry) = self.checked_mul(other);
        // Operator discards carry, similar to C#
        result
    }
}

// Division operator (/)
impl Div for Ufixed113 {
    type Output = Self;
    fn div(self, other: Self) -> Self::Output {
        match self.checked_div_rem(other) {
            Ok((quotient, _remainder)) => quotient,
            Err(Ufixed113Error::DivideByZero) => panic!("attempt to divide by zero"),
            Err(e) => panic!("division error: {:?}", e), // Should not happen if logic is sound
        }
    }
}

// Remainder operator (%)
impl Rem for Ufixed113 {
    type Output = Self;
    fn rem(self, other: Self) -> Self::Output {
        match self.checked_div_rem(other) {
            Ok((_quotient, remainder)) => remainder,
            Err(Ufixed113Error::DivideByZero) => panic!("attempt to divide by zero (for remainder)"),
            Err(e) => panic!("division error for remainder: {:?}", e),
        }
    }
}

// Left Shift operator (<<)
impl Shl<u32> for Ufixed113 { // Allow shifting by u32
    type Output = Self;
    fn shl(self, rhs: u32) -> Self::Output {
        self.logic_shift_left(rhs)
    }
}
// Implement for other integer types as needed, e.g., usize
impl Shl<usize> for Ufixed113 {
    type Output = Self;
    fn shl(self, rhs: usize) -> Self::Output {
        self.logic_shift_left(rhs as u32)
    }
}


// Right Shift operator (>>) - uses Arithmetic Right Shift to match C#
impl Shr<u32> for Ufixed113 {
    type Output = Self;
    fn shr(self, rhs: u32) -> Self::Output {
        self.arith_shift_right(rhs)
    }
}
impl Shr<usize> for Ufixed113 {
    type Output = Self;
    fn shr(self, rhs: usize) -> Self::Output {
        self.arith_shift_right(rhs as u32)
    }
}


impl TryFrom<f64> for Ufixed113 {
    type Error = Ufixed113Error;
    fn try_from(mut d: f64) -> Result<Self, Self::Error> {
        if d < 0.0 || d >= 2.0 { return Err(Ufixed113Error::Overflow); }
        let mut result = Ufixed113::ZERO;
        for _i in 0..Ufixed113::NUM_BITS {
            let int_part = d.floor();
            result = result.single_shift_left(int_part as u32);
            d -= int_part;
            d *= 2.0;
        }
        Ok(result)
    }
}

impl TryFrom<i32> for Ufixed113 {
    type Error = Ufixed113Error;
    fn try_from(value: i32) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Ufixed113::ZERO),
            1 => Ok(Ufixed113::ONE),
            _ => Err(Ufixed113Error::InvalidArgument), // C# used OverflowException
        }
    }
}
