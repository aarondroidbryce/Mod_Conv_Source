import data.zmod.basic
import data.finset
import tactic.fin_cases

--A set of necessary lemmas about the natural numbers to prove the first construction is valid
lemma div_mul_self_gt_sub (a b : ℕ) (h : b > 0): a - a/b * b < b := (nat.sub_lt_right_iff_lt_add (nat.div_mul_le_self a b)).2 (nat.lt_of_div_lt_div (by {rw [nat.add_mul_div_right b (a/b) h,nat.div_self h,add_comm,nat.add_one],exact nat.lt_succ_self _}))

def fin_sub_ge (a b : ℕ) (h : b > 0): {c : ℕ // c * b ≤ a ∧ a - c * b < b} := 
begin
  use a/b,
  exact ⟨nat.div_mul_le_self a b,div_mul_self_gt_sub a b h⟩,
end

lemma mod_sub_chain {a b c : ℕ} (h : c * b ≤ a ∧ a - c * b < b) (j : b > 0) : ∀ (n : ℕ), n ≤ c → ((a - n * b) % b = a % b) :=
begin
  intros n h₁,
  induction n,
  { simp, },
  { rw [←nat.add_one,nat.right_distrib,one_mul,← nat.sub_sub,← nat.mod_eq_sub_mod,n_ih (nat.le_of_succ_le h₁)],
    exact nat.le_sub_left_of_add_le (by { rw [←mul_one(b),←mul_assoc,mul_one,mul_comm,←nat.left_distrib,nat.add_one,mul_comm], exact le_trans (nat.mul_le_mul_right b h₁) h.1, } ) },
end

def sub_mod_eq_mul (a b : ℕ) (h : b > 0): {c : ℕ // a - a % b = b * c} :=
begin
  cases (fin_sub_ge a b h),
  use val,
  rw [←(mod_sub_chain property h val (le_of_eq rfl)),(nat.mod_eq_of_lt property.2),nat.sub_sub_self (property.1),mul_comm],
end

def eq_mod_add_mul (a b : ℕ) (h : b > 0): {c : ℕ // a = (a % b) + b * c} :=
begin
  cases (sub_mod_eq_mul a b h),
  use val,
  rw [←add_left_inj(a % b),←nat.add_sub_assoc(nat.mod_le a b),nat.add_sub_cancel_left] at property,
  exact property,
end

lemma mod_add_non_assoc {a b c : ℕ} (h : c > 0) : (a + b) % c = (a % c + b % c) % c :=
begin
  cases eq_mod_add_mul a c h,
  cases eq_mod_add_mul b c h,
  rw [property,property_1],
  simp[left_distrib],
  rw [←left_distrib,←add_assoc,nat.add_mul_mod_self_left],
end

lemma mod_add_left {a b c d : ℕ} (h : d > 0): b % d = c % d → (a + b) % d = (a + c) % d :=
λ h₁, by {rw [mod_add_non_assoc h,h₁,←mod_add_non_assoc h]}

--Simplest construction of what is trying to be proven under the % operator
def mod_conv (a : ℕ) (b c : ℕ+) : {d : ℕ // d < c ∧ (a % (b * c) = ( a % b + d * b ) % (b * c)) } :=
begin
  cases (eq_mod_add_mul a b (pnat.pos b)),
  use (val % c),
  split,
  { refine nat.mod_lt val (pnat.pos c), },
  { conv {to_lhs, rw property},
    exact mod_add_left (mul_pos (pnat.pos b) (pnat.pos c)) (by { rw [nat.mul_mod_mul_left b val c,mul_comm(val % c),nat.mul_mod_mul_left b (val % c) c,nat.mod_mod], }) },
end

--Equivalent construction in the zmod ring
--This is essentially just showing the definition is the same
def zmod_conv {a : ℕ} {b : ℕ+} {d : zmod b} (c : ℕ+) (h : (a : zmod b) = d) : {e : ℕ // (e ∈ finset.Ico 0 c ∧ (a : zmod (b * c)) = d.val + e * b.val)} :=
begin
  rcases mod_conv a b c,
  use val,
  have h₁ : (a : zmod (b * c)) = ((a % (↑b * ↑c) : ℕ) : zmod (b * c)) := by simp,
  simp[list.Ico.mem],
  simp[property,h₁],
  rw [←h,zmod.val_cast_nat],
  refl,
end

--A simple proof that for any integer there is a natural number with the same value mod b
--Namely that integer mod b considered as a natural number
def zmod_nat_from_int (a : ℤ) (b : ℕ+) : {c : ℕ // (c : zmod b) = (a : zmod b)} :=
begin
  use (a : zmod b).val,
  simp,
end

--A proof that equality in mod c×d implies equality in mod c
--This is true for both the left and right values however only this case was needed
lemma zmod_eq_of_zmod_mul_eq {a : ℤ} {b : ℕ} {c d : ℕ+} (h : (a : zmod (c * d)) = (b : zmod (c * d))) : (a : zmod c) = (b : zmod c) :=
begin
  have h₁ : ((c : ℕ) : ℤ) = (c : ℤ) := by simp,
  have h₂ : (a : zmod (c * d)) = ((b : ℤ) : zmod (c * d)) := by simp[h],
  have h₃  : a % (↑c * ↑d) = b % (↑c * ↑d) := zmod.eq_iff_modeq_int.1 h₂,
  rw [← int.mod_add_div a (c * d),← nat.mod_add_div b (c * d),h₃,← zmod.cast_mod_int,mul_assoc,h₁,int.add_mul_mod_self_left],
  conv {to_rhs, rw [← zmod.cast_mod_nat,mul_assoc,nat.add_mul_mod_self_left]},
  simp,
end

--The previous construction defined over all of the integers instead of only the natural numbers
def zmod_conv_int {a : ℤ} {b : ℕ+} {d : zmod b} (c : ℕ+) (h : (a : zmod b) = d) : {e : ℕ // (e ∈ finset.Ico 0 c ∧ (a : zmod (b * c)) = d.val + e * b.val)} :=
begin
  rcases zmod_nat_from_int a (b * c),
  rw ←h,
  rw [(zmod_eq_of_zmod_mul_eq property.symm)] at h,
  rcases zmod_conv c h,
  rw [(zmod_eq_of_zmod_mul_eq property.symm),←property,h],
  use val_1,
  exact property_1,
end

--An equivalency between zmod rings which are equal but have different represenations could not be constructed
--It was instead shown that equlaity in one ring implies equality inthe other ring
--It was then possible to convert equality statements between the rings 
lemma zmod_interchange {a b : ℤ } {c d e : ℕ+} (h : c = d * e) : (a : zmod (d * e)) = (b : zmod (d * e)) ↔ (a : zmod c) = (b : zmod c) :=
begin
  split,
  { intros h₁,
    rw [zmod.eq_iff_modeq_int,h,← zmod.eq_iff_modeq_int,h₁], },
  { intros h₂,
    rw [zmod.eq_iff_modeq_int,←h,← zmod.eq_iff_modeq_int,h₂], },
end

--An alternative form of the construction which takes a division hypothesis and uses this to generate the multplicative index
def zmod_conv_div {a : ℤ} {b c : ℕ+} {d : zmod b} (h : (a : zmod b) = d) (h₁ : (b : ℕ) ∣ (c : ℕ)) : {e : ℕ // (e ∈ finset.Ico 0 (c/b) ∧ (a : zmod c) = (((d.val + e * b.val) : ℕ) : zmod c))} :=
begin
  let f : ℕ+ := nat.to_pnat' ((c : ℕ)/(b : ℕ)),
  have h₂ : (c : ℕ) = b * f := by rw [← nat.div_eq_iff_eq_mul_right (pnat.pos b) h₁,pnat.to_pnat'_coe (nat.div_pos (nat.le_of_dvd (pnat.pos c) h₁) (pnat.pos b))],
  have h₃ : c = b * f := by rw [← pnat.coe_to_pnat' c,h₂,← pnat.mul_coe,pnat.coe_to_pnat'],
  have h₄ : (f : ℕ) = (c : ℕ)/(b : ℕ) := by rw pnat.to_pnat'_coe (nat.div_pos (nat.le_of_dvd (pnat.pos c) h₁) (pnat.pos b)),
  rcases zmod_conv_int f h,
  use val,
  let g : ℤ := (a : zmod b).val + val * b.val,
  have h₅ : (a : zmod c) = (g : zmod c) := (zmod_interchange h₃).1 (by simp[h,property.2]),
  rw [←h₄,h₅,←h],
  refine ⟨property.1,rfl⟩,
end

def int_to_pnat (z : ℤ) : ℕ+ := nat.to_pnat' (int.nat_abs z) --specifically for use with modular arithmatic, not a great coercion in a general context

section

local attribute [semireducible] reflected

meta instance pnat_reflect : has_reflect ℕ+
| n := expr.app `(nat.to_pnat') (nat.reflect n)

meta instance pnat_pexpr : has_to_pexpr ℕ+ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩

meta instance zmod_reflect {n : ℕ+} : has_reflect (zmod n)
| m := (nat.reflect m.val)

meta instance zmod_pexpr {n : ℕ+} : has_to_pexpr (zmod n) := ⟨pexpr.of_expr ∘ λ n, reflect n.val⟩

--Not sure why these next two are necessary, mathlib should have these but apply instance isn't finding them for some reason.

meta instance nat_pexpr : has_to_pexpr ℕ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩ 

meta instance int_pexpr : has_to_pexpr ℤ := ⟨pexpr.of_expr ∘ λ n, reflect n⟩ 

end

namespace tactic

namespace interactive

--Converts a hypothesis of the form (a ≡ b [ZMOD c]) to a hypothesis of the form (a : zmod c) = b)
--Will try to clear the orignal hypothesis if possible
--Rely's on the int_to_pnat map above to preserve modulo relationship if a negative integer is given
meta def eqmod_to_zmod (p : interactive.parse lean.parser.pexpr) : tactic unit :=
do  e ← i_to_expr p,
    `(%%α ≡ %%γ [ZMOD %%β]) ← infer_type e <|> fail ("Invalid Hypothesis : should be of type (_ ≡ _ [ZMOD _])"),
    b ← eval_expr ℤ β,
    a ← eval_expr ℤ α <|> eval_expr ℤ β,
    if a = b then do equi ← to_expr ```(((%%α : (zmod %%(reflect (int_to_pnat b)))) = %%γ)),
      tactic.assert e.local_pp_name equi,
      `[by {rw zmod.eq_iff_modeq_int, exact %%e}],
      tactic.clear e <|> trace ("Original hypothesis could not be removed due to dependency by another hypothesis")
    else do equi ← to_expr ```(((%%γ : (zmod %%(reflect (int_to_pnat b)))) = %%α)),
      tactic.assert e.local_pp_name equi,
      `[by {rw zmod.eq_iff_modeq_int, exact (%%e).symm}],
      tactic.clear e <|> trace ("Original hypothesis could not be removed due to dependency by another hypothesis")

--Converts a hypothesis of the form (a : zmod c) = b) to a hypothesis of the form (a ≡ b [ZMOD c])
--Will try to clear the orignal hypothesis if possible
--Can handle (a : zmod c) = b) or b = (a : zmod c) but will always return (a ≡ b [ZMOD c])
meta def zmod_to_eqmod (p : interactive.parse lean.parser.pexpr) : tactic unit :=
do  e ← i_to_expr p,
    α ← mk_mvar,
    β ← mk_mvar,
    γ ← mk_mvar,
    to_expr ``(_ : ((↑%%α : zmod %%β) = %%γ)) tt ff >>= unify e <|> to_expr ``(_ : %%γ = ((↑%%α : zmod %%β))) tt ff >>= unify e <|> fail ("Invalid Hypothesis1 : should be of type (_ : zmod _) = _)"),
    b ← eval_expr ℕ+ β,
    d ← eval_expr (zmod b) γ,
    equi ← to_expr ``(%%α ≡ (%%d.val : ℤ) [ZMOD ((%%β : ℕ) : ℤ)]),
    tactic.assert e.local_pp_name equi,
    `[by {rw ← zmod.eq_iff_modeq_int, exact %%e}] <|> `[by {rw ← zmod.eq_iff_modeq_int, exact (%%e).symm}],
    tactic.clear e <|> trace ("Original Hypothesis could not be removed due to dependency by another hypothesis")

--Tactic which applys the main construction from the above section
--Will try to clear the original hypothesis, after makingthe new construction
--Use of this as a temporary hypothesis is hardcoded, however does not appear to cause any naming conflicts
meta def apply_mod_conv (β : expr) (c : ℕ+) (e : expr) : tactic unit :=
do b ← eval_expr ℕ+ β,
  if (b : ℕ) ∣ c
  then do
    divproof ← to_expr ``(by norm_num : (%%(reflect b) : ℕ) ∣ %%(reflect c)),
    divtype ← infer_type divproof,
    divname ← get_unused_name,
    tactic.assertv divname divtype divproof,
    divhyp ← get_local divname,
    thmproof ← to_expr ```(zmod_conv_div %%e %%divhyp) <|> to_expr ```(zmod_conv_div (%%e).symm %%divhyp),
    thmtype ← infer_type thmproof,
    tactic.clear divhyp,
    let lname := e.local_pp_name,
    tactic.clear e <|> trace ("Original Hypothesis could not be removed due to dependency by another hypothesis"),
    tactic.assertv lname thmtype thmproof,
    hyp1 ← get_local lname,
    name1 ← get_unused_name,
    tactic.cases_core hyp1 [name1,lname],
    hyp2 ← get_local lname,
    name2 ← get_unused_name,
    tactic.cases_core hyp2 [name2,`this],
    hyp3 ← get_local name2,
    tactic.fin_cases_at none hyp3;
    zmod_to_eqmod ```(this);
    `[simp only [nat.to_pnat', int.coe_nat_zero, int.coe_nat_succ, nat.succ_pnat_coe, nat.pred_succ] at this];
    `[norm_num1 at this];
    tactic.rename `this lname
else fail ("Must input a multiple of the existing mod type")

--Interactive wrapper/guard for the apply sub_tactic
--Also handles the conversions between different acceptable input and output hypothesis
meta def mod_conv_tactic (p : interactive.parse lean.parser.pexpr) (c : ℕ+) : tactic unit :=
do e ← i_to_expr p,
  let l := e.local_pp_name,
  β ← mk_mvar,
  to_expr ``(_ : ((_ : zmod %%β) = _)) tt ff >>= unify e <|> to_expr ``(_ : _ ≡ _ [ZMOD %%β]) tt ff >>= unify e <|> fail ("Invalid Hypothesis : should be of type ((_ : zmod _) = _) or (_ ≡ _ [ZMOD _])"),
  b ← instantiate_mvars β,
  type ← infer_type b,
  if type = reflect ℕ+ then do apply_mod_conv b c e;
                            eqmod_to_zmod p  
  else do eqmod_to_zmod p,
  e ← i_to_expr p,
  β ← mk_mvar,
  to_expr ``(_ : ((_ : zmod %%β) = _)) tt ff >>= unify e,
  apply_mod_conv β c e

example {a : ℤ} (this : (a : zmod 15) = 6) : a = 2 :=
begin
mod_conv_tactic this 135, --135 is the largest input that works

end

example {a : ℤ} (r : (a ≡ 12 [ZMOD 17])) : a = 2 := --17 is the largest number to work with a value larger than 100 as input 
begin
mod_conv_tactic r 119,

end

example {a : ℤ} (r : (a ≡ 1 [ZMOD 2])) : a = 2 :=
begin
mod_conv_tactic r 104, --104 is the largest multiple of 2 which works, making 52 the maximum number of cases that works

end

example {a : ℤ} (thisr : (a ≡ 1 [ZMOD 41])) : a = 2 := --41 is the largest number that works as an initial value
begin
mod_conv_tactic thisr 82, --however it can only got up to 2 cases, 123 will fail

end

end interactive
end tactic