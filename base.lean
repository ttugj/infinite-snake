import algebra.lie_algebra
import algebra.module

import .words
import .ambient

namespace ambient_module

variables {M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M]

def serpentine (ζ : M) : Prop := ζ = E + (z 1) (σ (ζ + H))

namespace serpentine

variable {ζ : M} 

lemma invol (hζ : serpentine ζ) : τ ζ = -F + (z (-1)) (σ (τ ζ - H)) :=
begin -- suboptimal due to changes in base relation
    intros, unfold serpentine at hζ, conv_lhs { rw hζ },
    have h  : τ (E + ((z 1) (σ (ζ + H)))) = τ E + τ ((z 1) (σ (ζ + H))) := τ.add _ _,
    have h' : ∀ (x : M), τ ((z 1) (σ x)) = z (-1) (σ (τ x)) := begin
            intros,
            have k : ∀ (y : M), τ ((z 1) y) = z (-1) (τ y) := begin
                    intros,
                    have g := invol_circle 1,
                    simp [function.comp] at g,
                    apply_fun (λ (f : M → M), f y) at g,
                    rw g
                end,
            have k': ∀ (y : M), τ (σ y) = σ (τ y) := begin
                    intros,
                    have g := invol_shift,
                    simp [function.comp] at g,
                    apply_fun (λ (f : M → M), f y) at g,
                    rw g
                end,
            conv_lhs { rw k, rw k' }, 
        end, 
    have h'': τ (ζ + H) = τ ζ - H := begin
            have k : ∀ (x y : M), τ (x + y) = τ x + τ y := linear_map.map_add τ.to_linear_map,
            conv_lhs { rw k },
            simp [ invol_sl2.2 ],
            simp [ sub_eq_add_neg ] 
        end, 
    simp [h], rw invol_sl2.1, simp [h' (ζ + H)], simp [h'']
end

lemma act_H (hζ : serpentine ζ) : ⁅ H, ζ ⁆ = ζ :=
begin
    intros, 
    unfold serpentine at hζ,
    rw hζ,
    simp [lie_add, str_sl2],
    have h : (H : M) = (z 0) H := by simp [str_circle.1],
    rw h, 
    simp [sl2_circle],
    simp [(sl2_shift _ 0).2]
end

lemma act_H' (hζ : serpentine ζ) : ⁅ H, τ ζ ⁆ = -(τ ζ) :=
begin
    intros,
    rw (_ : H = -(-H)),
    rw ←(invol_sl2.2.1),
    rw neg_lie,
    erw ←τ.map_lie,
    rw act_H hζ, 
    simp [coe_fn, has_coe_to_fun.coe],
    simp
end

lemma act_E (hζ : serpentine ζ) : ⁅ E, ζ ⁆ = z 1 (ζ - E) :=
begin
    intros,
    unfold serpentine at hζ,
    rw hζ,
    simp [lie_add, str_sl2],
    have h : (E : M) = (z 0) E := by simp [str_circle.1],
    rw h, 
    simp [sl2_circle],
    simp [(sl2_shift _ 0).1],
    rw (by simp : ∀ (x : M), (z 1) ((z 1) x) = (linear_map.comp (z 1) (z 1)) x),
    simp [str_circle]
end

lemma act_F (hζ : serpentine ζ) : ⁅ F, ζ ⁆ = z (-1) (ζ - E) + 2 • H :=
begin
    intros,
    unfold serpentine at hζ,
    rw hζ,
    simp [lie_add, str_sl2],
    have h : (F : M) = (z 0) F := by simp [str_circle.1],
    rw h, 
    simp [sl2_circle],
    simp [(sl2_shift _ 0).2.2],
    rw (by simp : ∀ (x : M), (z (-1)) ((z 1) x) = (linear_map.comp (z (-1)) (z 1)) x),
    simp [str_circle],
    simp [add_comm]
end

lemma interpret_wt (hζ : serpentine ζ) : ∀ (w : words), ⁅ H, interpret ζ w ⁆ = w.wt • interpret ζ w :=
begin
    intros,
    let h := λ (b : words), ⁅ H, interpret ζ b ⁆ = b.wt • interpret ζ b,
    have hz : ∀ (a : gen), h (words.of a) := 
        begin
            intros, simp [h], erw (interpret_ze ζ a), simp [words.wt_ze], 
            cases a,
            simp [interpret_gen, words.wt_gen], exact (serpentine.act_H  hζ),
            simp [interpret_gen, words.wt_gen], exact (serpentine.act_H' hζ)
        end,
    have hs : ∀ (a : gen) (b : words), h (words.of a) → h b → h (words.of a * b) := 
        begin
            intros, simp [h], simp [h] at hz, erw (interpret_su ζ a b), 
            simp [words.wt_su], simp [words.wt_ze] at hz,
            erw (@transposed_jacobi M _ _ _ H _ _),
            simp [interpret_ze ζ] at hz,
            simp [hz],
            simp [h] at a_2,
            simp [a_2],
            cases a,
            simp [words.wt_gen, interpret_gen], conv_rhs { rw add_smul }, simp, -- A
            simp [words.wt_gen, interpret_gen], conv_rhs { rw add_smul }, simp  -- A'
        end,
    exact (free_semigroup.rec_on w hz hs)
end

end serpentine 

end ambient_module
