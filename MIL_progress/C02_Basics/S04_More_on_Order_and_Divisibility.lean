import MIL_progress.Common
import Mathlib.Data.Real.Basic

namespace C02S04
---柯里化是什么东西？？？
section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    · apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    · apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  --- apply是可以自动匹配参数的是吧？
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left


example : min (min a b) c = min a (min b c) := by
  sorry





theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

---将参数带入定理的方法很好，好用，利用这个构建一个新的命题
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h₁ := aux (a := a + c) (b := b + c) (c := -c)
  have h₂ : a + c + -c = a := by ring
  have h₃ : b + c + -c = b := by ring
  rw [h₂,h₃] at h₁
  linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
 have h := abs_add_le (a - b) b
 have h₁ : a - b + b = a := by ring
 rw [h₁] at h
 linarith
end
---有by与没有by,我在这里卡了很久，原题目是没有By的，这两种情况的区别在哪里？
section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h₁ : x ∣ w^2 := by
    apply dvd_pow
    exact h
    exact Ne.symm (Nat.zero_ne_add_one 1)
  have h₂ : x ∣ x ^ 2 := by
     apply dvd_mul_left
  have h₃ : x ∣ y * (x * z) := by
    apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  have h₄ :   x ∣ y * (x * z) + x ^ 2:= by
    apply dvd_add h₃ h₂
  apply dvd_add h₄ h₁


end

#check(dvd_add)
#check(dvd_pow)




section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  sorry
end
