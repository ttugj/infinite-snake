/- Definition and general properties of ambient modules. -/

import algebra.lie_algebra
import algebra.module
import algebra.free
import control.functor
import tactic
import data.int.parity

import .words

class ambient_module (M : Type) [lie_ring M] [lie_algebra ℤ M] :=
-- sl2 with half-H 
(E : M) (H : M) (F : M)
-- circle 
(z : ℤ → (module.End ℤ M)) 
-- shift
(σ : lie_algebra.morphism ℤ M M)
-- involution 
(τ : lie_algebra.morphism ℤ M M)
-- structure
(str_sl2 : ⁅H, E⁆ = E ∧ ⁅F, E⁆ = 2 • H ∧ ⁅H, F⁆ = -F)
(str_circle : z 0 = linear_map.id ∧ ∀ (i j : ℤ), linear_map.comp (z i) (z j) = z (i + j))
(str_invol : τ ∘ τ = id)
(invol_sl2 : τ E = -F ∧ τ H = -H ∧ τ F = -E)
(invol_circle : ∀ (i : ℤ), τ ∘ (z i) = z (-i) ∘ τ)
(invol_shift : τ ∘ σ = σ ∘ τ)
(sl2_shift : ∀ (m : M) (i : ℤ), 
               ⁅(z i) E, σ m⁆ = 0
             ∧ ⁅(z i) H, σ m⁆ = 0 
             ∧ ⁅(z i) F, σ m⁆ = 0)
(circle_shift : ∀ (m m' : M) (i j : ℤ), ⁅(z i) m, (z j) (σ m')⁆ = (z i) ⁅m, (z j) (σ m')⁆)
(sl2_circle : ∀ (i j : ℤ) (m : M), 
                ⁅(z i) E, (z j) m⁆ = j • (z (i+j+1)) m + (z j) ⁅(z i) E, m⁆ 
              ∧ ⁅(z i) H, (z j) m⁆ = j • (z (i+j  )) m + (z j) ⁅(z i) H, m⁆ 
              ∧ ⁅(z i) F, (z j) m⁆ = j • (z (i+j-1)) m + (z j) ⁅(z i) F, m⁆)

namespace ambient_module

variables {M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M]

instance ambient_invol : invol M := ⟨τ, str_invol⟩ 

def lift (f : gen → M) : words → M := 
words.rec f (λ a _ m, ⁅f a, m⁆)  

namespace lift

lemma ze : ∀ (f : gen → M) (a : gen), lift f (words.of a) = f a :=
begin
    intros, simp [lift, words.of, free_semigroup.of, words.rec, free_semigroup.rec_on] 
end

lemma su : ∀ (f : gen → M) (a : gen) (b : words), lift f (words.of a * b) = ⁅f a, lift f b⁆ :=
begin 
    intros, simp [lift, words.rec_su]
end

lemma invol 
    : ∀ (f : gen → M) (f_invol : ∀ (a : gen), f (gen.τ a) = τ (f a)) (w : words),
        lift f (invol.invol w) = τ (lift f w)
    :=
begin
    intros,
    let h :=  λ (b : words), lift f (invol.invol b) = invol.invol (lift f b),
    have hz : ∀ (a : gen), h (words.of a) :=
        begin
            intros,
            simp [h, lift],
            erw words.invol_of,
            simp [words.rec_ze],
            simp [f_invol],
            simp [invol.invol]
        end,
    have hs : ∀ (a : gen) (b : words), h (words.of a) → h b → h (words.of a * b) :=
        begin 
            intros, 
            simp [h] at a_2,
            simp [h],
            have ht : invol.invol (words.of a * b) = words.of a.τ * invol.invol b 
                    := by simpa [invol.invol, words.invol_of],
            simp [ht],
            repeat { erw lift.su },
            simp [a_2], 
            rw f_invol,
            simp [invol.invol]
        end,
    exact (free_semigroup.rec_on w hz hs)
end

end lift

def interpret_sl2_gen : gen → M
| gen.A  := E
| gen.A' := -F

def interpret_sl2 : words → M := lift interpret_sl2_gen

lemma interpret_sl2_gen_invol : ∀ (a : gen), interpret_sl2_gen (gen.τ a) = τ (interpret_sl2_gen a : M) :=
begin
    intros, cases a, 
    unfold gen.τ, unfold interpret_sl2_gen, simp [invol_sl2],
    unfold gen.τ, unfold interpret_sl2_gen, 
    have h : ∀ (x : M), τ (-x) = - τ x, swap, rw h, simp [invol_sl2],
    intros,
    exact (linear_map.map_neg (τ).to_linear_map x)
end 

lemma interpret_sl2_invol : ∀ (w : words), interpret_sl2 (invol.invol w) = invol.invol (interpret_sl2 w : M) :=
begin
    intros, unfold interpret_sl2, unfold invol.invol, 
    exact (lift.invol interpret_sl2_gen interpret_sl2_gen_invol w)
end

lemma interpret_sl2_ze : ∀ (a : gen), interpret_sl2 (words.of a) = (interpret_sl2_gen a : M) :=
begin
    intros, unfold interpret_sl2, simp [lift.ze]
end

lemma interpret_sl2_su : ∀ (a : gen) (w : words)
                       , interpret_sl2 (words.of a * w) = ⁅ (interpret_sl2_gen a : M), interpret_sl2 w ⁆ :=
begin
    intros, unfold interpret_sl2, simp [lift.su]
end

-- useful in rewriting expressions
lemma transposed_jacobi (x : M) : ∀ (y z : M), ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ :=
begin
    intros,
    rw ←(lie_skew x z), rw lie_neg,
    rw ←(lie_skew ⁅x, y⁆ z),
    rw add_comm,
    have h : ∀ (a b c : M), a + b + c = 0 → a = -b + -c := 
        begin
            intros, rw add_assoc at a_1, rw @eq_neg_of_add_eq_zero M _ a (b + c) a_1, simp [add_comm]  
        end,
    apply h, exact lie_ring.jacobi x y z,
end  

lemma transposed_jacobi' (x : M) : ∀ (y z : M), ⁅⁅y, z⁆,x⁆ = ⁅⁅y, x⁆, z⁆ + ⁅y, ⁅z, x⁆⁆ :=
begin
    intros, rw ←(lie_skew ⁅y, z⁆ x), erw ←(lie_skew y x), erw ←(lie_skew z x),
    erw lie_neg, erw neg_lie, conv_lhs { erw transposed_jacobi x y z }, simp [add_comm]
end

-- a simplified version of sl2_circle
lemma sl2_circle' : ∀ (m : M) (j : ℤ),
                        ⁅E, (z j) m⁆ = j • (z (j+1)) m + (z j) ⁅E, m⁆ 
                      ∧ ⁅H, (z j) m⁆ = j • (z (j  )) m + (z j) ⁅H, m⁆ 
                      ∧ ⁅F, (z j) m⁆ = j • (z (j-1)) m + (z j) ⁅F, m⁆
:= 
begin 
    have hE : (E : M) = (z 0) E := by simp [str_circle.1],
    have hH : (H : M) = (z 0) H := by simp [str_circle.1],
    have hF : (F : M) = (z 0) F := by simp [str_circle.1],
    intros, split,
    erw hE, simp [sl2_circle],
    split,
    erw hH, simp [sl2_circle],
    erw hF, simp [sl2_circle],
end

section zeta 

variable (ζ : M)

def interpret_gen : gen → M
| gen.A  := ζ
| gen.A' := τ ζ

def interpret  : words → M := lift (interpret_gen ζ)

lemma interpret_ze : ∀  (a : gen), interpret ζ (words.of a) = interpret_gen ζ a :=
begin intros, unfold interpret, simp [lift.ze] end

lemma interpret_su : ∀  (a : gen) (b : words)
                   , interpret ζ (words.of a * b) = ⁅interpret_gen ζ a, interpret ζ b⁆ :=
begin intros, unfold interpret, simp [lift.su] end

lemma interpret_gen_invol : ∀  (a : gen), interpret_gen ζ (gen.τ a) = τ (interpret_gen ζ a) :=
begin
    intros, cases a, simpa [interpret_gen], rw (gen.τ), simp [interpret_gen],
    have h := str_invol,
    simp [function.comp] at h,
    apply_fun (λ (f : M → M), f ζ) at h,
    rw h
end 

lemma interpret_invol : ∀  (w : words), interpret ζ (invol.invol w) = invol.invol (interpret ζ w) :=
begin
    intros, unfold interpret, unfold invol.invol, 
    exact (lift.invol (interpret_gen ζ) (interpret_gen_invol ζ) w)
end

end zeta


def Φ (i : ℤ) (y x : M) := ⁅ y, z i x ⁆ - z i ⁅ y, x ⁆ 

lemma Φ_str : ∀ (i : ℤ) (y y' x : M), 
              Φ i ⁅ y, y' ⁆ x = ⁅ y, Φ i y' x ⁆ + ⁅ Φ i y x, y' ⁆ + Φ i y ⁅ y', x ⁆  - Φ i y' ⁅ y, x ⁆ :=
begin
    intros, unfold Φ, 
    conv_lhs { rw transposed_jacobi' },
    conv_lhs { rw transposed_jacobi' x },
    simp [sub_eq_add_neg, lie_add],
    erw ←(lie_skew (⁅ _ , x ⁆)  _),
    erw ←(lie_skew (⁅ _ , z i x ⁆)  _),
    erw ←(lie_skew (z i ⁅ _ , x ⁆)  _),
    erw ←(lie_skew (z i ⁅ y , x ⁆) y'),
    repeat { rw ←add_assoc },
    rw linear_map.map_neg,
    have h : ∀ (a b c d e f : M), a + -b + -c + d + b + -e + f + -d = -c + a + -e - -f := begin intros, abel end, 
    conv_rhs { rw h }, refl,
end

lemma Φ_gen (a : gen) : ∀ (i : ℤ) (x : M), Φ i (interpret_sl2_gen a) x = (i * words.wt_gen a) • z (words.wt_gen a + i) x
:=
begin
    intros, unfold Φ, cases a,
    unfold interpret_sl2_gen, rw (sl2_circle' x i).1, unfold words.wt_gen, rw add_comm 1 i, simp,
    unfold interpret_sl2_gen, rw neg_lie, rw (sl2_circle' x i).2.2, unfold words.wt_gen, 
    rw neg_add_eq_sub, rw neg_add, rw neg_lie, rw linear_map.map_neg, simp
end

lemma interpret_sl2_μ (w : words) : 
∀ (i : ℤ) (x : M) , Φ i (interpret_sl2 w) x = (w.μ * i) • z (w.wt + i) x 
:= /- note: the definition of μ had been simplified, so the proof is suboptimal -/
begin
    let h := λ (b : words), ∀ (i : ℤ) (x : M), Φ i (interpret_sl2 b) x = (b.μ * i) • z (b.wt + i) x,
    have hz : ∀ (a : gen), h (words.of a) := 
        begin
            simp [h], intros, rw interpret_sl2_ze, rw (Φ_gen a i x),
            rw words.wt_ze, rw words.μ_ze, simp [mul_comm]
        end,
    have hs : ∀ (a : gen) (b : words), h (words.of a) → h b → h (words.of a * b) :=
        begin
            simp [h], intros, 
            rw interpret_sl2_su, rw interpret_sl2_ze at a_1, 
            rw (Φ_str i),
            simp [a_2, a_1], 
            simp [words.μ_ze],
            simp [words.μ_su],
            have h' : ∀ (p q r s : M), p + q + r - s = (p - s) - (-q - r) := begin intros, abel end,
            have h'' : ∀ (c : ℤ) (p q : M), c • p - c • q = c • (p - q) := begin intros, rw ←smul_sub  end, 
            have fold_Φ : ∀ (j : ℤ) (y : M), ⁅ y, z j x ⁆ - z j ⁅ y, x ⁆ = Φ j y x := begin intros, unfold Φ end,
            conv_lhs { 
                rw h', rw ←smul_neg, rw (lie_skew (interpret_sl2 b) _),
                rw h'', rw h'', 
                rw fold_Φ, rw fold_Φ
            },
            simp [a_2, a_1],
            simp [words.wt_su, words.wt_ze, words.μ_ze],
            rw ←mul_smul, rw ←mul_smul,
            conv_lhs { congr, congr, skip, rw ←add_assoc },
            conv_lhs { congr, skip, congr, skip, rw ←add_assoc, rw (add_comm b.wt _) },
            have h3 : ∀ (c d : ℤ) (y : M), c • y -  d • y = (c - d) • y := begin intros, rw ←sub_smul  end, 
            have h4 : ∀ (c d : ℤ) (y : M), c = d → c • y = d • y := begin intros, rw a_3 end, 
            rw h3,
            apply h4,
            repeat { rw ←mul_assoc },
            repeat { rw mul_add }, 
            repeat { rw mul_sub },
            repeat { rw sub_mul },
            repeat { rw ←mul_assoc },
            cases a,
            unfold words.wt_gen, ring,
            unfold words.wt_gen, ring
        end,
    exact (free_semigroup.rec_on w hz hs)
end


end ambient_module

-- ⁅    ⁆
