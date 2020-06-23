import algebra.free
import control.functor
import tactic

class invol (α : Type) := (invol : α → α) (invol_eq : invol ∘ invol = id)

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

lemma rec_map : ∀ {α : Type} (ze : gen → α) (su : gen → words → α → α) (f : gen → gen) (w : words),
                rec ze su (f <$> w) = rec (λ a, ze (f a)) (λ a w, su (f a) (f <$> w)) w :=
begin
    intros, simp [rec, free_semigroup.rec_on],
    have h : ∀ (w' : words), f <$> w' = (f w'.1, f <$> w'.2),
    swap, erw h, cases w, 
    simp,
    induction w_snd generalizing w_fst,
    simp [list.map],
    simp [list.map],
    erw [w_snd_ih],
    simp [h],
    intro, 
    simp [functor.map, function.comp],
    cases w', simp,
    induction w'_snd generalizing w'_fst,
    unfold free_semigroup.lift,
    unfold free_semigroup.lift',
    unfold free_semigroup.of,
    simp,
    unfold list.map,
    unfold free_semigroup.lift,
    unfold free_semigroup.lift',
    unfold free_semigroup.of,
    simp,
    unfold free_semigroup.lift at w'_snd_ih,
    unfold free_semigroup.of at w'_snd_ih,
    simp at w'_snd_ih,
    simp [w'_snd_ih],
    simpa [free_semigroup.mul]
end 

def ell_gen : gen → ℕ := (λ _, 1)
def wt_gen  : gen → ℤ 
| gen.A  :=  1
| gen.A' := -1

def ell : words → ℕ := rec (λ _, 1) (λ _ _ l, l.succ)
def wt  : words → ℤ := rec wt_gen   (λ a _ k, wt_gen a + k) 
def μ   : words → ℤ := rec wt_gen   (λ a w m, (1 - wt_gen a * wt w) * m) 

-- involutivity properties of ell, wt, μ...
lemma ell_invol : ∀ (w : words), ell (invol.invol w) = ell w :=
begin
    intros, unfold invol.invol, unfold ell, simp [rec_map]
end

lemma wt_gen_invol : ∀ (a : gen), wt_gen (gen.τ a) = -(wt_gen a) := 
begin
    intros, induction a,
    simp [gen.τ, wt_gen],
    simp [gen.τ, wt_gen],
end

lemma wt_invol : ∀ (w : words), wt (invol.invol w) = -(wt w) :=
begin 
    intros, unfold invol.invol, unfold wt,
    simp [rec_map, wt_gen_invol],
    unfold rec,
    induction w,
    unfold free_semigroup.rec_on,
    induction w_snd generalizing w_fst,
    simp,
    simp [w_snd_ih],
    simp [add_comm]
end

lemma wt_invol' : ∀ (w : words), wt (gen.τ <$> w) = -(wt w) :=
begin
    intros, 
    have h := wt_invol w,
    unfold invol.invol at h,
    exact h
end

lemma μ_invol : ∀ (w : words), μ (invol.invol w) = -(μ w) :=
begin
    intros, unfold μ,
    unfold invol.invol, simp [rec_map, wt_gen_invol, wt_invol'],
    unfold rec,
    induction w,
    unfold free_semigroup.rec_on,
    induction w_snd generalizing w_fst,
    simp,
    simp [w_snd_ih]
end

end words
