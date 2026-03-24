import Mathlib
open Real
-- 你可以在下面添加自己的证明练习！
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- 设 `m` 和 `n` 是自然数，设 `n = 2 * k`
  rintro m n ⟨k, hk⟩
  -- 需证 `m * n` 是某自然数的两倍。那就设它是 `m * k` 的两倍吧
  use m * k
  -- 代入 `n`
  rw [hk]
  -- 剩下的就很显然了
  ring

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [←mul_assoc]
  rw [h]
  ring


example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
 rw[hyp]
 rw[hyp']
 ring

section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a*(c+d)+b*(c+d) := by
     rw [add_mul]
    _ =a * c + a * d + b * c + b * d := by
     rw [mul_add,mul_add]
     ring
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring







#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)









#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring





end


namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc]
  nth_rw 2 [add_comm]
  rw [neg_add_cancel]
  rw [add_zero]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

end MyRing

#check MyRing.add_zero
#check add_zero





example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  -- le_trans : a ≤ b → b ≤ c → a ≤ c, `a ≤ c` 匹配到了目标 `x ≤ z`
  -- 于是 `a` 被重命名（正式地：“实例化”）为 `x`，`c`被重命名为 `z`，
  -- `b` 尚未得到它的新名字，因此处在“元变量”（metavariable）状态，表示为 `?b`
  -- 接下来两个前提 `x ≤ ?b`，`?b ≤ z` 成为了新目标
  · apply h₀
  · apply h₁
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

example {a b : ℝ} (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

example {a} : 0 ≤ a ^ 2 := by
   exact sq_nonneg a


example {a b : ℝ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2:=
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example (a b : ℝ) : min a b = min b a := by
  apply le_antisymm

  apply le_min
  apply min_le_right
  apply min_le_left
  
  apply le_min
  apply min_le_right
  apply min_le_left
