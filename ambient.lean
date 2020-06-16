import algebra.lie_algebra
import algebra.module
import algebra.free
import control.functor
import tactic

class invol (α : Type) := (invol : α → α) (invol_eq : invol ∘ invol = id)

class ambient_module (k : Type) (M : Type) 
[comm_ring k] [lie_ring M] [lie_algebra k M] :=
-- sl2 with half-H 
(E : M) (H : M) (F : M)
-- circle 
(z : ℤ → (module.End k M)) 
-- shift
(σ : lie_algebra.morphism k M M)
-- involution 
(τ : lie_algebra.morphism k M M)
-- structure
(str_sl2 : ⁅H, E⁆ = E ∧ ⁅F, E⁆ = 2 • H ∧ ⁅H, F⁆ = -F)
(str_circle : z 0 = linear_map.id ∧ ∀ (i j : ℤ), z i ∘ z j = z (i + j))
(str_invol : τ ∘ τ = id)
(invol_sl2 : τ E = -F ∧ τ H = -H ∧ τ F = -E)
(invol_circle : ∀ (i : ℤ), τ ∘ (z i) = z (-i))
(invol_shift : τ ∘ σ = σ ∘ τ)
(sl2_shift : ∀ (m : M) (i j : ℤ), 
               ⁅(z i) E, (z j) (σ m)⁆ = 0
             ∧ ⁅(z i) H, (z j) (σ m)⁆ = 0 
             ∧ ⁅(z i) F, (z j) (σ m)⁆ = 0)
(circle_shift : ∀ (m m' : M) (i j : ℤ), ⁅(z i) m, (z j) (σ m')⁆ = (z i) ⁅m, (z j) (σ m')⁆)
(sl2_circle : ∀ (i j : ℤ) (m : M), 
                ⁅(z i) E, (z j) m⁆ = j • (z (i+j+1)) m + (z j) ⁅(z i) E, m⁆ 
              ∧ ⁅(z i) H, (z j) m⁆ = j • (z (i+j  )) m + (z j) ⁅(z i) H, m⁆ 
              ∧ ⁅(z i) F, (z j) m⁆ = j • (z (i+j-1)) m + (z j) ⁅(z i) F, m⁆)

namespace ambient_module

variables (k : Type) [comm_ring k]

instance ambient_invol {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] : invol M :=
⟨@τ k _ _ _ _ _, @str_invol k _ _ _ _ _⟩ 

def is_serpentine 
{M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M]  -- lots of instances here...
(ζ : M) : Prop :=
(ζ = E k + (@z k _ _ _ _ _ 1) (@σ k _ _ _ _ _ (ζ - H k))) 

end ambient_module

inductive gen | A : gen | A' : gen
def words := free_semigroup gen

namespace gen

def τ : gen → gen | A := A'| A' := A

def τ_eq : τ ∘ τ = id :=
begin rw function.comp, funext, cases x, unfold τ, simp, unfold τ, simp, end

instance : invol gen := ⟨τ, τ_eq⟩

end gen


namespace words 

instance : invol words := ⟨functor.map gen.τ, begin rw functor.map_comp_map, rw ←functor.map_id, rw gen.τ_eq, end⟩

instance [c : semigroup (free_semigroup gen)] : semigroup words := begin unfold words, exact c end

def of (a : gen) : words := free_semigroup.of a 

lemma invol_of : ∀ (a : gen), invol.invol (of a) = of (gen.τ a) :=
begin
    simp [invol.invol, of, functor.map]
end

-- simple recursor
def rec {α : Type} (ze : gen → α) (su : gen → words → α → α) (w : words) : α :=
@free_semigroup.rec_on gen 
        (λ _,  α) w 
        (λ (a : gen), ze a) 
        (λ (a : gen) (w : words) (_ r : α), su a w r)

lemma rec_ze { α : Type } : ∀ (ze : gen → α) (su : gen → words → α → α) (a : gen),
                            rec ze su (of a) = ze a :=
begin
    unfold rec, unfold free_semigroup.rec_on, intros, simpa [of]
end 

lemma rec_su { α : Type } : ∀ (ze : gen → α) (su : gen → words → α → α) (w : words) (a : gen),
                            rec ze su (of a * w) = su a w (rec ze su w) :=
begin
    unfold rec, intros, unfold free_semigroup.rec_on,
    have h' : of a * w = (a, w.1 :: w.2),
    swap,
    cases w,
    erewrite h',
    simpa [semigroup.mul],
end 

end words

namespace ambient_module

variables (k : Type) [comm_ring k]

def interpret_gen {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] (ζ : M) : gen → M
| gen.A  := ζ
| gen.A' := @τ k _ _ _ _ _ ζ

def interpret {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] (ζ : M) : words → M := 
words.rec (interpret_gen k ζ) (λ a _ m, ⁅interpret_gen k ζ a, m⁆)  

lemma interpret_of {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] :
    ∀ (ζ : M) (a : gen), interpret k ζ (words.of a) = interpret_gen k ζ a :=
begin
    intros, simp [interpret, words.of, free_semigroup.of, words.rec, free_semigroup.rec_on] 
end

lemma interpret_su {M :Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] :
    ∀ (ζ : M) (a : gen) (b : words), interpret k ζ (words.of a * b) = ⁅interpret_gen k ζ a, interpret k ζ b⁆ :=
begin 
    intros, simp [interpret, words.rec_su]
end

lemma interpret_gen_invol {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] : 
    ∀ (ζ : M) (a : gen), interpret_gen k ζ (gen.τ a) = @τ k _ _ _ _ _ (interpret_gen k ζ a) :=
begin
    intros, cases a, simpa [interpret_gen], rw (gen.τ), simp [interpret_gen],
    have h := @str_invol k M _ _ _ _,
    simp [function.comp] at h,
    apply_fun (λ (f : M → M), f ζ) at h,
    rw h
end 

lemma interpret_invol  {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] :
    ∀ (ζ : M) (w : words), interpret k ζ (invol.invol w) = invol.invol (interpret k ζ w)
:= 
begin
    intros,
    let h :=  λ (b : words), interpret k ζ (invol.invol b) = invol.invol (interpret k ζ b),
    have hz : ∀ (a : gen), h (words.of a) :=
        begin
            intros,
            simp [h, interpret],
            erewrite words.invol_of,
            simp [words.rec_ze],
            simp [interpret_gen_invol],
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
            repeat { erw interpret_su },
            simp [a_2], 
            rw interpret_gen_invol,
            simp [invol.invol]
        end,
    exact (@free_semigroup.rec_on 
                gen 
                (λ (w' : words), interpret k ζ (invol.invol w') = invol.invol (interpret k ζ w')) 
                w hz hs),
end

end ambient_module

namespace words

def ell_gen : gen → ℕ := (λ _, 1)
def wt_gen  : gen → ℤ 
| gen.A  :=  1
| gen.A' := -1

def ell : words → ℕ := rec (λ _, 1) (λ _ _ l, l.succ)
def wt  : words → ℤ := rec wt_gen   (λ a _ k, wt_gen a + k) 
def μ   : words → ℤ := rec wt_gen   (λ a w m, (1 - wt_gen a * wt w) * m) 

-- involutivity properties of ell, wt, μ...

end words
