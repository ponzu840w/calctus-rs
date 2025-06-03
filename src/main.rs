// main.rs

mod ufixed113;
use ufixed113::UFixed113;

fn main() {
    // ライブラリ内の assert を使ったテストをひとまず実行
    UFixed113::test();
    println!("基本テスト (assert) にすべて合格しました。");

    // いくつか例を表示してみる
    // 1 + 1
    let (sum, carry1) = UFixed113::ONE.add(&UFixed113::ONE);
    println!("1 + 1 → 結果: {:?}, キャリー: {}", sum, carry1);

    // 1 - 1
    let (diff, borrow1) = UFixed113::ONE.sub(&UFixed113::ONE);
    println!("1 - 1 → 結果: {:?}, 借り下がり: {}", diff, borrow1);

    // 0 - 1 (アンダーフロー)
    let (under, borrow2) = UFixed113::ZERO.sub(&UFixed113::ONE);
    println!("0 - 1 → 結果: {:?}, 借り下がり: {}", under, borrow2);
}
