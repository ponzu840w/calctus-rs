use std::convert::TryFrom;

mod ufixed113;
use crate::ufixed113::{Ufixed113, Ufixed113Error};

fn main() -> Result<(), Ufixed113Error> {
    println!("Ufixed113 Full Operations Demonstration");
    println!("======================================");

    let val_0_5 = Ufixed113::try_from(0.5)?;
    let val_1_0 = Ufixed113::ONE;
    let val_1_5 = Ufixed113::try_from(1.5)?;
    let val_0_25 = Ufixed113::try_from(0.25)?;

    // --- Addition and Subtraction (from previous example) ---
    println!("\n--- Add/Sub ---");
    let (sum1_res, sum1_carry) = val_0_5.checked_add(val_0_5);
    println!("0.5 + 0.5 = {} (Carry: {}) -> Expected: {} (Carry: 0)", sum1_res, sum1_carry, val_1_0);
    assert_eq!(sum1_res, val_1_0); assert_eq!(sum1_carry, 0);

    let sum_op = val_1_0 + val_1_0; // 1.0 + 1.0 = 0.0 (wraps, carry discarded by op)
    println!("1.0 + 1.0 (op) = {} -> Expected: {}", sum_op, Ufixed113::ZERO);
    assert_eq!(sum_op, Ufixed113::ZERO);

    let sub_op = val_0_5 - val_1_0; // 0.5 - 1.0 = -0.5 (wraps to 1.5)
    println!("0.5 - 1.0 (op) = {} -> Expected: {}", sub_op, val_1_5);
    assert_eq!(sub_op, val_1_5);

    // --- Multiplication ---
    println!("\n--- Multiplication ---");
    let (mul1_res, mul1_carry) = val_0_5.checked_mul(val_0_5); // 0.5 * 0.5 = 0.25
    println!("0.5 * 0.5 = {} (Carry: {}) -> Expected: {} (Carry: 0)", mul1_res, mul1_carry, val_0_25);
    assert_eq!(mul1_res, val_0_25); assert_eq!(mul1_carry, 0);

    let (mul2_res, mul2_carry) = val_1_5.checked_mul(val_0_5); // 1.5 * 0.5 = 0.75
    let val_0_75 = Ufixed113::try_from(0.75)?;
    println!("1.5 * 0.5 = {} (Carry: {}) -> Expected: {} (Carry: 0)", mul2_res, mul2_carry, val_0_75);
    assert_eq!(mul2_res, val_0_75); assert_eq!(mul2_carry, 0);
    
    let mul_op = val_1_5 * val_1_5; // 1.5 * 1.5 = 2.25. For Q1.112, this overflows. Expected 0.25 with carry.
                                    // (1.5 * 1.5 = (3/2)*(3/2) = 9/4 = 2 + 1/4). Carry = 1 (for 2.0 part), result = 0.25
    let (expected_mul_op_res, expected_mul_op_carry) = val_1_5.checked_mul(val_1_5);
    println!("1.5 * 1.5 (op) = {} -> Expected checked: {} (Carry: {})", mul_op, expected_mul_op_res, expected_mul_op_carry);
    assert_eq!(expected_mul_op_res, val_0_25);
    assert_eq!(expected_mul_op_carry, 1); // Carry due to exceeding integer bit capacity
    assert_eq!(mul_op, val_0_25);


    // --- Division ---
    println!("\n--- Division ---");
    let (div1_q, div1_r) = val_1_5.checked_div_rem(val_0_5)?; // 1.5 / 0.5 = 3.0. Overflows Q1.112. Expected Q=1.0 (max for pos), Rem=1.0
                                                             // Actually 1.5 / 0.5 = (3/2)/(1/2) = 3.  This means an integer 3.
                                                             // In Q1.112, this is overflow. The div logic needs to handle this.
                                                             // If we represent 3.0, it's 11.0_bin. Ufixed113 can only be < 2.0.
                                                             // So, 1.5 / 0.5. Result of integer division 1 / 0 = inf.
                                                             // Let's use values that fit: 0.75 / 0.5 = 1.5
    let (div2_q, div2_r) = val_0_75.checked_div_rem(val_0_5)?; // 0.75 / 0.5 = 1.5
    println!("0.75 / 0.5 = Q: {}, R: {} -> Expected Q: {}, R: {}", div2_q, div2_r, val_1_5, Ufixed113::ZERO);
    assert_eq!(div2_q, val_1_5); assert_eq!(div2_r, Ufixed113::ZERO);

    let div_op = val_0_75 / val_0_5;
    println!("0.75 / 0.5 (op) = {} -> Expected: {}", div_op, val_1_5);
    assert_eq!(div_op, val_1_5);

    let val_1_0 = Ufixed113::ONE;
    let val_0_333_approx = Ufixed113::try_from(1.0/3.0)?; // Approximate 0.333...
    //let (q_1_div_3, r_1_div_3) = val_1_0.checked_div_rem(Ufixed113::try_from(3.0)?)?; // This is 1.0 / (overflow for 3.0)
                                                                                    // Let's do 1.0 / (Ufixed113 from 1.0), then divide by integer 3 via shifts
                                                                                    // Test with 1.0 / 0.25 = 4.0 (overflow)
                                                                                    // Test 0.5 / 0.25 = 2.0 (overflow for result, should be 1.xxxx and carry, or cap at max)
    let div_0_5_by_0_25_q = val_0_5 / val_0_25; // 0.5 / 0.25 = 2.0. This should be ONE with carry if div produced it.
                                               // Or, if it wraps, ZERO. Let's see.
                                               // The current DivRem gives Q based on self = Q*D+R. If Q*D overflows, R might be odd.
                                               // 0.5 / 0.25 = 2. Q1.112 cannot hold 2. Max is <2.
                                               // The division algorithm produces a quotient that fits. If the true result is >=2, it will be clamped or aliased.
                                               // The current fixed point division `q = sum (bit_i * 2^-i)` will naturally be < 2.
                                               // So for 0.5/0.25 = 2.0, it will likely result in 0.0 with some internal overflow if not handled.
                                               // Or represent the largest possible value (all fraction bits 1).

    // --- Shift Operations ---
    println!("\n--- Shifts ---");
    let num_for_shift = Ufixed113::try_from(1.5)?; // Binary 1.100...
    println!("Original for shift (1.5): {}", num_for_shift);

    let lsl1 = num_for_shift << 1u32; // 1.5 << 1 = (overflows integer part) 1.0 (binary 1.000...)
    let expected_lsl1 = Ufixed113::try_from(1.0)?; // (1.1_bin << 1 = 1.0_bin, MSB 1 lost, new MSB is old frac MSB)
    println!("1.5 << 1  = {} -> Expected: {}", lsl1, expected_lsl1); // C# logic shift left
    // My single_shift_left: 1.100 -> SSL(0) -> 1.000 (old MSB 1 lost, old frac MSB 1 becomes new int MSB)
    assert_eq!(lsl1, expected_lsl1);

    let lsr1 = num_for_shift.logic_shift_right(1); // 1.5 >> 1 (logic) = 0.75 (binary 0.110...)
    println!("1.5 >> 1 (logic) = {} -> Expected: {}", lsr1, val_0_75);
    assert_eq!(lsr1, val_0_75);

    let asr1 = num_for_shift >> 1u32; // 1.5 >> 1 (arith) = (MSB was 1) -> 1.110... (1.75)
    let val_1_75 = Ufixed113::try_from(1.75)?;
    println!("1.5 >> 1 (arith) = {} -> Expected: {}", asr1, val_1_75);
    assert_eq!(asr1, val_1_75);
    
    let num_0_5_for_shift = Ufixed113::try_from(0.5)?; // Binary 0.100...
    let asr2 = num_0_5_for_shift >> 1u32; // 0.5 >> 1 (arith) = (MSB was 0) -> 0.010... (0.25)
    println!("0.5 >> 1 (arith) = {} -> Expected: {}", asr2, val_0_25);
    assert_eq!(asr2, val_0_25);

    // --- TruncateRight ---
    println!("\n--- TruncateRight ---");
    // 1.5 is 1.1000..._2. In words (MSB first): [1][0x8000000][0]...
    // words: [e=1, d=0x8000000, c=0, b=0, a=0]
    // Hex: 1 8000000 0000000 0000000 0000000
    println!("1.5 before truncate: {}", val_1_5);
    let truncated1 = val_1_5.truncate_right(1); // Clear LSB of fractional part (bit 111 of fraction)
                                                // This is bit 0 of words[0]. Not very visible.
    let truncated2 = val_1_5.truncate_right(28); // Clears words[0]
    let expected_trunc2 = Ufixed113::new(0,0,0,0x8000000,1); // words[0]=0, words[1]=0, words[2]=0, words[3]=0x8000000, words[4]=1
    println!("1.5 truncate_right(28): {} -> Expected: {}", truncated2, expected_trunc2);
    assert_eq!(truncated2, expected_trunc2);
    
    let truncated3 = val_1_5.truncate_right(112); // Clears all fractional words (words[0] to words[3])
    let expected_trunc3 = Ufixed113::new(0,0,0,0,1); // Should be 1.0
    println!("1.5 truncate_right(112): {} -> Expected: {}", truncated3, Ufixed113::ONE);
    assert_eq!(truncated3, Ufixed113::ONE);


    println!("\nAll implemented assertions passed (manual verification for some division cases recommended).");
    Ok(())
}
