import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL_progress.Common

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)---为什么是箭头？
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end
---前面的一段check是有深意的，lean里面apply定理更像是寻找参数，它在自己匹配合适的参数
---在第一个例子里面先apply le_trans,唯一只有x<=z匹配到到了定理的需要的参数，a=x,z=c,而b没有匹配的参数，所以x ≤ ?b和?b ≤ z两个goal,但是第三个是什么鬼？
---在第二个例子里面 相当于先把h0作为参数提前传入le_trans了
--- 现在还有的疑问是，第一种情况中的第三个goals是为什么出现，在第二个里面没有；还有参数是以什么条件匹配的？顺序？或者其他？；还有参数究竟是什么？a b c?定理？
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁
---这里没有使用apply，而是直接输入定理
example (x : ℝ) : x ≤ x := by
  apply le_refl

--把R改为N之后，goal里面⊢ 的也改了
example (x : ℕ) : x ≤ x :=
  le_refl x


#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Try this.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h₄ : a < c := by
    apply lt_of_le_of_lt h₀ h₁
  have h₅ : c < e := by
    apply lt_of_le_of_lt h₂ h₃
  apply lt_trans h₄ h₅


---have对于把目标拆开很好用



example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
---好评
end

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have h₁ : a + d ≤ a + e := by
    apply add_le_add_right h₀
  linarith [exp_le_exp.2 h₁]


example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    linarith [exp_pos a]
  apply log_le_log h₀
  have h₁ : 1 + exp a ≤ 1 + exp b := by
    apply add_le_add_right
    apply exp_le_exp.mpr h
  exact h₁




---apply?

example : 0 ≤ a ^ 2 := by
  exact sq_nonneg a


example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  have h₀ : exp a ≤ exp b := by
    apply exp_le_exp.mpr h
  apply add_le_add_right
  apply neg_le_neg
  exact h₀
---这里的原文省略了:=by 虽然没有错误但是又warning
example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 := by
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example  : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 := by
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
  have h₁ :a*b ≤ (a^2 + b^2)/2 := by
    have h : 0 ≤ a^2 - 2*a*b + b^2 := by
      calc
       a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
    linarith
  have h₂ : -(a*b) ≤ (a^2 + b^2)/2 := by
    have h : 0 ≤ a^2 + 2*a*b + b^2 := by
      calc
        a^2 + 2*a*b + b^2 = (a + b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
    linarith
  apply abs_le'.mpr
  constructor
  · exact h₁
  · exact h₂




#check abs_le'.mpr
