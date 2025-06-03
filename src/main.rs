use std::convert::TryFrom;

// ufixed113.rs が main.rs と同じディレクトリにある場合:
mod ufixed113;
use crate::ufixed113::{Ufixed113, Ufixed113Error};

fn main() -> Result<(), Ufixed113Error> {
    println!("Ufixed113 Demostration (Add and Subtract)");
    println!("-----------------------------------------");

    // C# Test: AssertAdd(0.5, 0.5, 1, 0u);
    let val_0_5 = Ufixed113::try_from(0.5)?;
    let val_1_0 = Ufixed113::try_from(1.0)?;
    // let val_0_0 = Ufixed113::ZERO; // Ufixed113::try_from(0.0)?;

    println!("Value 0.5: {}", val_0_5); // Expected: representation of 0.5
    println!("Ufixed113::ONE (1.0): {}", Ufixed113::ONE); // Expected: 0 0000000 0000000 0000000 10000000 (incorrect expectation here, should be 1 at MSB)
                                                        // Correct for 1.0 (ONE): 1 0000000 0000000 0000000 0000000

    let (sum1_res, sum1_carry) = val_0_5.checked_add(val_0_5);
    println!("0.5 + 0.5 = {} (Expected: {}) with carry: {} (Expected: 0)", sum1_res, val_1_0, sum1_carry);
    assert_eq!(sum1_res, val_1_0);
    assert_eq!(sum1_carry, 0);

    // C# Test: AssertAdd(1, 1, 0, 1u);
    let (sum2_res, sum2_carry) = Ufixed113::ONE.checked_add(Ufixed113::ONE);
    println!("1.0 + 1.0 = {} (Expected: {}) with carry: {} (Expected: 1)", sum2_res, Ufixed113::ZERO, sum2_carry);
    assert_eq!(sum2_res, Ufixed113::ZERO);
    assert_eq!(sum2_carry, 1);

    // Using the '+' operator (discards carry)
    let sum_op = Ufixed113::ONE + Ufixed113::ONE;
    println!("1.0 + 1.0 (operator) = {} (Expected: {})", sum_op, Ufixed113::ZERO);
    assert_eq!(sum_op, Ufixed113::ZERO);


    // C# Test: AssertSub(1, 1, 0, 0u);
    let (sub1_res, sub1_borrow) = Ufixed113::ONE.checked_sub(Ufixed113::ONE);
    println!("1.0 - 1.0 = {} (Expected: {}) with borrow: {} (Expected: 0)", sub1_res, Ufixed113::ZERO, sub1_borrow);
    assert_eq!(sub1_res, Ufixed113::ZERO);
    assert_eq!(sub1_borrow, 0);

    let val_0_25 = Ufixed113::try_from(0.25)?;
    let (sub2_res, sub2_borrow) = val_0_5.checked_sub(val_0_25); // 0.5 - 0.25
    let expected_sub2_res = Ufixed113::try_from(0.25)?;
    println!("0.5 - 0.25 = {} (Expected: {}) with borrow: {} (Expected: 0)", sub2_res, expected_sub2_res, sub2_borrow);
    assert_eq!(sub2_res, expected_sub2_res);
    assert_eq!(sub2_borrow, 0);
    
    // Test subtraction with borrow
    let (sub3_res, sub3_borrow) = val_0_25.checked_sub(val_0_5); // 0.25 - 0.5
    // Expected result for 0.25 - 0.5 is -0.25.
    // In 2's complement for Q1.112, -0.25 would be ~0.25 + 1_lsb.
    // Ufixed113::ONE (1.0) is 1 0...0
    // Ufixed113::try_from(1.75)? would be 1.110...0 which is -0.25 if it were signed Q.112
    // Since this is unsigned, 0.25 - 0.5 will wrap around.
    // -0.25 + 2.0 (modulus) = 1.75
    let expected_sub3_res_wrap = Ufixed113::try_from(1.75)?;

    println!("0.25 - 0.5 = {} (Expected wrap: {}) with borrow: {} (Expected: 1)", sub3_res, expected_sub3_res_wrap, sub3_borrow);
    assert_eq!(sub3_res, expected_sub3_res_wrap);
    assert_eq!(sub3_borrow, 1);

    // Using the '-' operator (discards borrow)
    let sub_op = val_0_25 - val_0_5;
    println!("0.25 - 0.5 (operator) = {} (Expected wrap: {})", sub_op, expected_sub3_res_wrap);
    assert_eq!(sub_op, expected_sub3_res_wrap);

    println!("\nDemonstration of Negation:");
    let neg_0_5 = -val_0_5;
    // -0.5 + 2.0 = 1.5
    let expected_neg_0_5 = Ufixed113::try_from(1.5)?;
    println!("-0.5 = {} (Expected: {})", neg_0_5, expected_neg_0_5);
    assert_eq!(neg_0_5, expected_neg_0_5);
    
    // Check if 0.5 + (-0.5) == 0
    let sum_with_neg = val_0_5 + neg_0_5; // 0.5 + 1.5 (mod 2)
    println!("0.5 + (-0.5) = {} (Expected: {})", sum_with_neg, Ufixed113::ZERO);
    assert_eq!(sum_with_neg, Ufixed113::ZERO);


    println!("\nAll assertions passed successfully!");
    Ok(())
}
