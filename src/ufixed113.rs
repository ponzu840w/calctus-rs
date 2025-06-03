use std::fmt;
use std::ops::{Add, Sub, Not, Neg};
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
}

#[derive(Debug, Copy, Clone, Eq)]
pub struct Ufixed113 {
    // words[0] is LSW (Least Significant Word of fractional part)
    // words[MSB_WORD_INDEX] is MSW (Most Significant Word, 1-bit integer part)
    words: [u32; N_WORDS],
}

impl Ufixed113 {
    pub const NUM_BITS: usize = 113;

    // C# new ufixed113(e, d, c, b, a) where a=_words[0], e=_words[4]
    // Rust new(a,b,c,d,e) where a=words[0], e=words[4]
    pub const fn new(a: u32, b: u32, c: u32, d: u32, e: u32) -> Self {
        Self {
            words: [
                a & MASK_28BIT,
                b & MASK_28BIT,
                c & MASK_28BIT,
                d & MASK_28BIT,
                e & 1, // MSB word (e) is 1 bit
            ],
        }
    }

    pub const ZERO: Self = Self { words: [0, 0, 0, 0, 0] };
    // C# One = new ufixed113(1u, 0u, 0u, 0u, 0u) -> e=1, a=b=c=d=0 -> _words = [0,0,0,0,1]
    pub const ONE: Self = Self { words: [0, 0, 0, 0, 1] };
    // Represents the smallest fractional value, 2^-112. Used for 2's complement.
    // new ufixed113(0u,0u,0u,0u,1u) in C# -> a=1, rest 0 -> _words = [1,0,0,0,0]
    const ONE_LSB: Self = Self { words: [1, 0, 0, 0, 0] };


    // Helper for TryFrom<f64>
    // Shifts self 1 bit to the left, and inserts carry_bit_for_lsb0 into the LSB position.
    fn single_shift_left(mut self, carry_bit_for_lsb0: u32) -> Self {
        debug_assert!(carry_bit_for_lsb0 <= 1);
        let mut current_carry_to_next_word_lsb = carry_bit_for_lsb0;

        for i in 0..N_WORDS {
            let original_word_val = self.words[i];
            let new_lsb_for_this_word = current_carry_to_next_word_lsb;

            if i == MSB_WORD_INDEX { // MSB word (1 bit)
                // The old MSB bit is shifted out (lost).
                self.words[i] = new_lsb_for_this_word & 1;
                // current_carry_to_next_word_lsb = original_word_val & 1; // This would be the bit shifted out
            } else { // Normal 28-bit words
                current_carry_to_next_word_lsb = (original_word_val >> (WORD_BITS - 1)) & 1; // MSB of this word
                self.words[i] = ((original_word_val << 1) & MASK_28BIT) | new_lsb_for_this_word;
            }
        }
        self
    }

    /// Performs addition: self + other.
    /// Returns (result, carry_out).
    /// carry_out is 1 if the addition overflowed the 113-bit range, 0 otherwise.
    pub fn checked_add(self, other: Self) -> (Self, u32) {
        let mut accum_words = [0u32; N_WORDS];
        let mut carry_from_prev_word: u32 = 0;

        for i in 0..N_WORDS {
            let mut current_sum = (self.words[i] as u64) + (other.words[i] as u64) + (carry_from_prev_word as u64);

            if i == MSB_WORD_INDEX {
                // For MSB word, store the sum temporarily. Final handling is done after loop.
                // This sum might be > 1 if there's a carry and both MSBs are 1.
                accum_words[i] = current_sum as u32;
                // carry_from_prev_word = (current_sum >> 1) as u32; // Carry out of this 1-bit word. Not used in C# loop struct
            } else {
                accum_words[i] = (current_sum & (MASK_28BIT as u64)) as u32;
                carry_from_prev_word = (current_sum >> WORD_BITS) as u32;
            }
        }

        // Finalize MSB word and determine overall carry_out, mirroring C# logic
        // accum_words[MSB_WORD_INDEX] currently holds sum for the MSB position (e.g. 0,1,2,3)
        let final_carry_out = (accum_words[MSB_WORD_INDEX] >> 1) & 1; // Bit 1 is carry
        accum_words[MSB_WORD_INDEX] &= 1;                             // Bit 0 is result MSB

        (Self { words: accum_words }, final_carry_out)
    }

    /// Performs arithmetic inversion (2's complement negation).
    /// Returns (result, carry_out_of_inversion).
    /// The carry_out is typically ignored for negation itself but useful for subtraction.
    pub fn arith_invert(self) -> (Self, u32) {
        let inverted = !self; // Bitwise NOT
        inverted.checked_add(Ufixed113::ONE_LSB) // Add 1 (at LSB position)
    }

    /// Performs subtraction: self - other.
    /// Returns (result, borrow_out).
    /// borrow_out is 1 if self < other (a borrow was needed), 0 otherwise.
    pub fn checked_sub(self, other: Self) -> (Self, u32) {
        let borrow_out = if self < other { 1 } else { 0 };
        // Subtraction a - b is a + (-b)
        // -b is arith_invert(b)
        let (neg_other, _neg_carry) = other.arith_invert();
        let (result, _add_carry) = self.checked_add(neg_other);
        // Note: The _add_carry from a + (-b) relates to overflow of that sum,
        // not directly to the borrow in the traditional sense of a-b.
        // The borrow_out determined by self < other is more conventional.
        (result, borrow_out)
    }
}

impl PartialEq for Ufixed113 {
    fn eq(&self, other: &Self) -> bool {
        self.words == other.words
    }
}

impl PartialOrd for Ufixed113 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ufixed113 {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare from MSB word down to LSB word
        for i in (0..N_WORDS).rev() {
            if self.words[i] > other.words[i] {
                return Ordering::Greater;
            }
            if self.words[i] < other.words[i] {
                return Ordering::Less;
            }
        }
        Ordering::Equal
    }
}


impl fmt::Display for Ufixed113 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // MSB word (1 bit, C# shows as 1 hex digit)
        write!(f, "{:x}", self.words[MSB_WORD_INDEX])?;
        // Other words (28 bits, C# shows as 7 hex digits)
        for i in (0..MSB_WORD_INDEX).rev() {
            write!(f, " {:07x}", self.words[i])?;
        }
        Ok(())
    }
}

// Bitwise NOT operator (~)
impl Not for Ufixed113 {
    type Output = Self;
    fn not(self) -> Self::Output {
        let mut result_words = [0u32; N_WORDS];
        for i in 0..N_WORDS {
            result_words[i] = self.words[i] ^ MASK_28BIT; // XOR with 28 ones
        }
        // MSB word is only 1 bit, so ensure it's masked correctly after full XOR
        result_words[MSB_WORD_INDEX] &= 1;
        Self { words: result_words }
    }
}

// Unary Negation operator (-)
impl Neg for Ufixed113 {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.arith_invert().0 // Discard carry for the Neg operator
    }
}

// Addition operator (+)
impl Add for Ufixed113 {
    type Output = Self;
    fn add(self, other: Self) -> Self::Output {
        let (result, carry) = self.checked_add(other);
        if carry != 0 {
            // This behavior matches C# operator+ which discards carry and wraps.
            // For strict overflow checking, use checked_add directly.
            // Alternatively, panic here or return Result from operator.
            // For now, mimic C#'s implicit wrap for the operator.
        }
        result
    }
}

// Subtraction operator (-)
impl Sub for Ufixed113 {
    type Output = Self;
    fn sub(self, other: Self) -> Self::Output {
        let (result, _borrow) = self.checked_sub(other);
        // Similar to Add, operator Sub discards borrow information.
        result
    }
}

impl TryFrom<f64> for Ufixed113 {
    type Error = Ufixed113Error;

    fn try_from(mut d: f64) -> Result<Self, Self::Error> {
        // This type represents values in [0, 2.0)
        // because it's Q1.112 (1 integer bit, 112 fractional bits).
        if d < 0.0 || d >= 2.0 {
            return Err(Ufixed113Error::Overflow);
        }

        let mut result = Ufixed113::ZERO;
        // Iterate NumBits times to fill all bits from MSB to LSB of the target.
        // The double `d` is processed by taking its floor (integer part for the current bit position)
        // and then shifting it left into the `result`.
        for _i in 0..Ufixed113::NUM_BITS {
            let int_part = d.floor(); // This will be 0 or 1 as d is progressively < 2.0
            result = result.single_shift_left(int_part as u32);
            d -= int_part; // Remove the part we just processed
            d *= 2.0;      // Shift next bit of `d` into integer position for next iteration
        }
        Ok(result)
    }
}
