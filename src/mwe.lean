import algebra.big_operators.pi
import algebra.module.pi
import algebra.module.linear_map
import algebra.big_operators.ring
import algebra.star.basic
import data.fintype.card
import data.matrix.dmatrix
import linear_algebra.matrix.symmetric
import linear_algebra.matrix
import linear_algebra.matrix.trace
import linear_algebra.matrix.to_lin
import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic 
import linear_algebra.eigenspace 
import tactic.find
import analysis.normed.group.basic
import analysis.inner_product_space.pi_L2

run_cmd tactic.skip
--set_option trace.simplify true
--set_option trace.simplify.rewrite_failure false 
--set_option trace.linarith true

universe u

variables {α n m R : Type*} [fintype n] [fintype m] [decidable_eq n] [has_neg α]

namespace matrix

open_locale matrix

open_locale complex_order complex_conjugate

instance : has_coe (n → ℝ) (n → ℂ) := ⟨λ x, (λ i, ⟨x i, 0⟩)⟩
instance : has_coe (matrix m n ℝ) (matrix m n ℂ) := ⟨λ M, (λ i j, ⟨M i j, 0⟩)⟩

-- The conjugate of a vector is obtained by taking the conjugate of each element of the vector
def vector_conj (v : n → ℂ) : n → ℂ := λ i : n, conj (v i)

-- The matrix conjugate is obtained by taking the conjugate of each element of the matrix
def matrix_conj (M : matrix n n ℂ) : matrix n n ℂ := λ i : n, vector_conj (M i)

-- An eigenpair of M is a pair (e, v) such that v ≠ 0 and M v = e v
def has_eigenpair (M : matrix n n ℂ) (e : ℂ) (v : n → ℂ ) := v ≠ 0 ∧ mul_vec M v = e • v 

-- A vector which is part of an eigenpair of M is called an eigenvector of M
def has_eigenvector (M : matrix n n ℂ) (v : n → ℂ ) := ∃ e : ℂ , has_eigenpair M e v

-- A number which is part of an eigenpair of M is called an eigenvalue of M
def has_eigenvalue (M : matrix n n ℂ) (e : ℂ) := ∃ v : n → ℂ , has_eigenpair M e v

-- A left eignpair of M is a pair (e, v) such that v ≠ 0 and vᵀ M = vᵀ e  
def has_left_eigenpair (M : matrix n n ℂ) (e : ℂ) (v : n → ℂ ) := v ≠ 0 ∧ vec_mul v M = e • v 

-- A vector which is part of an eigenpair of M is called a left eigenvector of M
def has_left_eigenvector (M : matrix n n ℂ) (v : n → ℂ ) := ∃ e : ℂ , has_left_eigenpair M e v

-- A number which is part of an eigenpair of M is called a left eigenvalue of M
def has_left_eigenvalue (M : matrix n n ℂ) (e : ℂ) := ∃ v : n → ℂ , has_left_eigenpair M e v

-- A matrix is caleed skew-symmetric if its transpose is equal to its negative
def is_skew_symmetric (M : matrix n n α ) := Mᵀ = -M

-- ∑ Re(f (v i)) = Re(∑ f (v i)) 
lemma sum_re {v : n → ℂ} {f : ℂ → ℂ }: finset.univ.sum (λ i, (f (v i)).re) = (finset.univ.sum (λ i, f(v i))).re:=
begin
  rw ← complex.re_lm_coe,
  rw linear_map.map_sum,
end

-- ∑ Im(f (v i)) = Im(∑ f (v i))
lemma sum_im {v : n → ℂ} {f : ℂ → ℂ }: finset.univ.sum (λ i, (f (v i)).im) = (finset.univ.sum (λ i, f(v i))).im:=
begin
  rw ← complex.im_lm_coe,
  rw linear_map.map_sum,
end

-- ∑ (f (v i))' = (∑ f (v i))'
lemma sum_conj_func {v : n → ℂ } {f : ℂ → ℂ }: conj (finset.univ.sum (λ i, f (v i))) = finset.univ.sum (λ i, conj (f (v i))) :=
begin
  ext,
  rw complex.conj_re,
  rw ← sum_re,
  change finset.univ.sum (λ (i : n), (conj (f (v i))).re) = (finset.univ.sum (λ (i : n), conj (f (v i)))).re,
  rw sum_re,
  rw ← sum_im,
  simp only [complex.conj_im, finset.sum_neg_distrib, neg_inj],
  rw sum_im, 
end

-- ∑ (v i)' = (∑ (v i))'
lemma sum_conj {v : n → ℂ} : conj (finset.univ.sum (λ i, (v i))) = finset.univ.sum (λ i, conj ((v i))) :=
begin
  
  have h : conj (finset.univ.sum (λ i, id (v i))) = finset.univ.sum (λ i, conj (id (v i))), 
  {exact sum_conj_func},

  dsimp at h,
  exact h,
end

-- (a * b)' = a' * b'
lemma mul_conj (a : ℂ ) (b : ℂ ) : conj (a * b) = (conj a) * (conj b) :=
begin
  ext,
  simp only [complex.mul_re, complex.conj_re, complex.conj_im, mul_neg, neg_mul, neg_neg],
  simp only [complex.mul_im, neg_add_rev, complex.conj_re, complex.conj_im, mul_neg, neg_mul],
  rw add_comm,
end

-- (vᵀv)' = ((v')ᵀv')
lemma dot_product_conj (v : n → ℂ) (w : n → ℂ) : conj (dot_product v w) = dot_product (vector_conj v) (vector_conj w) :=
begin
  repeat {rw dot_product},
  repeat {rw vector_conj},
  dsimp only,
  rw sum_conj,
  apply finset.sum_congr,
  refl,
  intros _ _,
  rw mul_conj,
end

-- (vᵀM)' = (v')ᵀM'
lemma vec_mul_conj (v : n → ℂ) (M : matrix n n ℂ) : vector_conj (vec_mul v M) = vec_mul (vector_conj v) (matrix_conj M):=
begin
  
  have vm : vec_mul (vector_conj v) M.matrix_conj = λ i , dot_product (vector_conj v) (λ j, conj (M j i)),
  {
    ext;
    rw vec_mul;
    rw dot_product;
    rw dot_product;
    rw matrix_conj;
    simp only;
    rw vector_conj;
    simp only;
    simp_rw vector_conj
  },
  
  rw vm,
  ext;
  rw vector_conj;
  rw vector_conj;
  dsimp only;
  rw vec_mul;
  rw dot_product_conj;
  repeat {rw vector_conj},
end

-- (Mv)' = M'v' 
lemma mul_vec_conj (v : n → ℂ) (M : matrix n n ℂ) : vector_conj (mul_vec M v) = mul_vec (matrix_conj M) (vector_conj v) :=
begin
  have mv : mul_vec (matrix_conj M) (vector_conj v) = λ i , dot_product (vector_conj v) (λ j, conj (M i j)),
  {
    ext;
    rw mul_vec;
    rw dot_product;
    rw dot_product;
    rw matrix_conj;
    simp only;
    rw vector_conj;
    simp only;
    simp_rw mul_comm
  },

  rw mv,
  ext;
  rw vector_conj;
  rw vector_conj;
  dsimp only;
  rw mul_vec;
  rw dot_product_conj;
  repeat {rw vector_conj};
  simp_rw dot_product;
  simp_rw mul_comm,
end

-- v'' = v
lemma vector_conj_conj (v : n → ℂ) : vector_conj (vector_conj v) = v := 
begin
  apply funext,
  rw vector_conj,
  intro x,
  rw vector_conj,
  change conj (conj (v x)) = v x,
  rw complex.conj_conj,
end  

-- M'' = M
lemma matrix_conj_conj (M : matrix n n ℂ) : matrix_conj (matrix_conj M) = M := 
begin
  apply funext,
  rw matrix_conj,
  rw matrix_conj,
  intro x,
  change vector_conj (vector_conj (M x)) = M x,
  rw vector_conj_conj,
end 

-- (x • v)' = x' • v'
lemma vec_smul_conj (v : n → ℂ) (x : ℂ) : vector_conj (x • v) = (conj x) • (vector_conj v) :=
begin
  repeat {rw vector_conj},
  simp only [pi.smul_apply, algebra.id.smul_eq_mul, map_mul],
  simp_rw mul_conj,
  refl,
end

-- (x • M)' = x' • M'
lemma mat_smul_conj (M : matrix n n ℂ) (x : ℂ) : matrix_conj (x • M) = (conj x) • (matrix_conj M):=
begin
  repeat {rw matrix_conj},
  funext,
  dsimp,
  rw vec_smul_conj,
  rw pi.smul_apply,
  rw algebra.id.smul_eq_mul,
end

-- (M + N)' = M' + N'
lemma mat_add_conj (M : matrix n n ℂ) (N : matrix n n ℂ ) : matrix_conj (M + N) = matrix_conj M + matrix_conj N :=
begin
  funext,
  repeat {rw matrix_conj},
  dsimp,
  repeat {rw vector_conj},
  dsimp,
  rw map_add,
end

-- (M - N)' = M' - N'
lemma mat_sub_conj (M : matrix n n ℂ) (N : matrix n n ℂ ) : matrix_conj (M - N) = matrix_conj M - matrix_conj N :=
begin
  funext,
  repeat {rw matrix_conj},
  dsimp,
  repeat {rw vector_conj},
  dsimp,
  rw map_sub,
end

-- M' i j = (M i j)'
lemma mat_conj_apply (M : matrix n n ℂ) (i j : n): M.matrix_conj i j = (conj (M i j)) :=
begin
  simp_rw matrix_conj,
  rw vector_conj,
end

-- (M ⬝ N)' = M' ⬝ N'
lemma mat_mul_conj (M N : matrix n n ℂ) : (M ⬝ N).matrix_conj = M.matrix_conj ⬝ N.matrix_conj :=
begin
  funext,
  rw matrix.mul_apply,
  rw mat_conj_apply,
  rw matrix.mul,
  simp_rw dot_product,
  rw sum_conj,
  simp_rw mul_conj,
  simp_rw mat_conj_apply,
end 

-- (Mᵀv) = (vM)ᵀ
lemma mul_vec_trans (M : matrix n n ℂ ) (v : n → ℂ ) : (mul_vec Mᵀ v) = (vec_mul v M) :=
begin
  ext;
  rw mul_vec;
  rw vec_mul;
  rw dot_product;
  rw dot_product;
  simp_rw matrix.transpose;
  rw finset.sum_congr,
  refl,
  intros _ _,
  rw mul_comm,
  refl,
  intros _ _,
  rw mul_comm,
end

-- vᵀMᵀ = (Mv)ᵀ 
lemma vec_mul_trans (M : matrix n n ℂ) (v : n → ℂ ) :  (vec_mul v Mᵀ ) = mul_vec M v :=
begin
  have h : M.mul_vec v = Mᵀᵀ.mul_vec v,
  rw transpose_transpose,
  rw h,
  rw mul_vec_trans,
end

-- (M - N)v = Mv - Nv
lemma sub_mul_vec (M N : matrix n n ℂ) (v : n → ℂ ) : (M - N).mul_vec v = M.mul_vec v - N.mul_vec v:=
begin
  repeat {rw sub_eq_add_neg},
  rw add_mul_vec,
  rw add_right_inj,
  funext,
  repeat{rw mul_vec},
  simp only [pi.neg_apply],
  rw mul_vec,
  simp_rw dot_product,
  rw ← finset.sum_neg_distrib,
  rw finset.sum_congr,
  refl,
  intros _ _,
  rw neg_mul,
end

-- Mᵀ' = M'ᵀ
lemma matrix_trans_conj (M : matrix n n ℂ) : (matrix_conj Mᵀ) = (matrix_conj M)ᵀ :=
begin
  funext,
  rw matrix_conj,
  rw transpose_apply,
  dsimp,
  rw vector_conj,
  rw matrix_conj,
  dsimp,
  rw vector_conj,
end 

-- (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ
lemma matrix_mul_trans (M N : matrix n n ℂ) : (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ :=
begin
  funext i j,
  rw transpose_apply,
  repeat {rw matrix.mul},
  dsimp,
  rw dot_product_comm,
  refl,
end

-- (M ⬝ Mᵀ) = (M ⬝ Mᵀ)ᵀ 
lemma prod_transpose_symm (M : matrix n n ℂ) : (M ⬝ Mᵀ)=(M ⬝ Mᵀ)ᵀ :=
begin
  rw eq_comm,
  rw matrix_mul_trans,
  rw transpose_transpose,
end

noncomputable def vector_sq_mag (v : n → ℂ) : ℂ := (dot_product (vector_conj v) v)

-- (v')ᵀv ≥ 0
lemma vector_sq_mag_geq_zero (v : n → ℂ) : vector_sq_mag v ≥ 0 :=
begin
   rw vector_sq_mag,
   rw dot_product,
   
   -- ∀ i, (v' i) (v i) ≥ 0
   have h : ∀ (x : n), conj (v x) * (v x) ≥ 0,
   {
     intro x,
     
     have h_im : (conj (v x) * (v x)).im = (0:ℂ).im,
     {
       rw complex.mul_im,
       rw complex.conj_re,
       rw complex.conj_im,
       rw complex.zero_im,
       nlinarith, -- Re(v x) * Im(v x) + - Im(v x) * Re(v x) = 0
     },

    have h_re : (conj (v x) * (v x)).re ≥ (0:ℂ).re,
    {
      rwa complex.mul_re,
      rwa complex.conj_re,
      rwa complex.conj_im,
      rw neg_mul,
      rw sub_neg_eq_add,
      rw complex.zero_re,
      nlinarith,  -- Re(v x) * Re(v x) + Im(v x) * Im(v x) ≥ 0
    },

    rw [ge,complex.le_def],
    split,
    assumption, -- h_re
    rw eq_comm,
    assumption, -- h_im
   },

  apply finset.sum_nonneg,  -- ∀ i, 0 ≤ (v' i) * (v i) 
  intro x,
  intro _,
  specialize h x,
  rw ← ge,
  exact h,
end

-- (v')ᵀv ∈ ℝ
lemma vector_sq_mag_real (v : n → ℂ ) : vector_sq_mag v = (vector_sq_mag v).re :=
begin
  ext,
  rw complex.of_real_re,
  
  have h := vector_sq_mag_geq_zero v,
  
  rw [ge,complex.le_def] at h,
  cases h with h_re h_im,
  rw complex.of_real_im,
  rw ← h_im,
  rw complex.zero_im,
end

-- (v')ᵀv = 0 ↔ v = 0
theorem vector_zero_iff_sq_mag_zero (v : n → ℂ) : vector_sq_mag v = 0 ↔ v=0 := 
begin
  rw vector_sq_mag,
  split,
  intro prod,
  rw dot_product at prod,

  -- (v i) * (v' i) ≥ 0
  have gez : ∀ i : n, v i * vector_conj v i ≥ 0,
  {
    intro i,
    rw vector_conj,
    dsimp,
    rw ge_iff_le,
    rw complex.le_def,
    split,
    rw complex.mul_re,
    simp only [complex.zero_re, complex.conj_re, complex.conj_im, mul_neg, sub_neg_eq_add],
    nlinarith,  -- 0 ≤ Re(v i) * Re(v i) + Im(v i) * Im(v i)
    rw complex.mul_im,
    rw complex.conj_im,
    rw complex.conj_re,
    simp only [complex.zero_im, mul_neg],
    rw mul_comm,
    rw add_left_neg,
  },

  have important : finset.univ.sum(λ i , v i * vector_conj v i ) = 0 ↔ ∀ i ∈ finset.univ, v i * vector_conj v i = 0,
  {
    apply finset.sum_eq_zero_iff_of_nonneg, -- ∀ i, 0 ≤ (v i) * (v' i)
    intros i _,
    specialize gez i,
    rw ge_iff_le at gez,
    exact gez
  },

  simp_rw mul_comm at prod,
  rw prod at important,
  simp only [eq_self_iff_true, finset.mem_univ, mul_eq_zero, forall_true_left, true_iff] at important,
  funext i,
  specialize important i,
  cases important with vz vcz,
  rw vz,
  refl,
  rw vector_conj at vcz,
  dsimp at vcz,
  
  have vczc := congr_arg conj vcz,
  
  rw [complex.conj_conj] at vczc,
  simp only [map_zero] at vczc,
  rw vczc, 
  refl,
  intro ez,
  rw ez,
  rw dot_product_comm,
  rw zero_dot_product,
end

-- |x • v| = x²|v|
lemma smul_sq_mag (x : ℂ) (v: n → ℂ ) (h : x.im = 0): vector_sq_mag (x • v) = (x * x) * vector_sq_mag v :=
begin
  rw vector_sq_mag,
  rw vec_smul_conj,
  
  simp only [dot_product_smul, smul_dot_product, algebra.id.smul_eq_mul, monoid_with_zero_hom.coe_mk, complex.of_real_add,
  complex.of_real_mul],
  rw ← vector_sq_mag,
  rw ← mul_assoc,
  
  rw star_ring_end_apply,
  
  suffices x_star : star x = x,
  {rw x_star},

  unfold star,
  ext,
  refl,
  rw h,
  rw neg_zero,
end

-- A vector is real iff it is equal to its conjugate
lemma vector_eq_conj_iff_real (v : n → ℂ) : (∃ u : n → ℝ, v = u) ↔ v = vector_conj v :=
begin
  split,
  intro h,
  cases h with u veq,
  funext,
  rw vector_conj,
  dsimp,
  rw veq,
  rw eq_comm,
  rw complex.eq_conj_iff_real,
  use u x,
  refl,
  intro veq,
  use (λ i , (v i).re ),
  funext,
  
  have vx_re : v x = (v x).re,
  {
    ext,
    rw complex.of_real_re,
    rw complex.of_real_im,
    rw ← add_self_eq_zero,
    nth_rewrite 0 veq,
    rw vector_conj,
    dsimp,
    rw add_left_neg
  },

  rw vx_re,
  refl,
end

-- A matrix is real iff it is equal to its conjugate  
lemma matrix_eq_conj_iff_real (M : matrix n n ℂ) : (∃ N : matrix n n ℝ, M = N) ↔ M = matrix_conj M :=
begin
  split,
  intro h,
  cases h with N eq,
  rw eq,
  funext,
  rw matrix_conj,
  simp_rw vector_conj,
  rw eq_comm,
  rw complex.eq_conj_iff_real,
  use N i j,
  refl,
  
  intro meq,
  use (λ (i_1 i_2 : n), (M i_1 i_2).re),
  funext i j,
  
  have mij_conj : M i j = conj (M i j),
  {
    nth_rewrite 0 meq,
    rw matrix_conj,
    dsimp,
    rw vector_conj,
  },
  
  have mij_re : M i j = (M i j).re,
  {
    ext,
    rw complex.of_real_re,
    rw complex.of_real_im,
    rw ← add_self_eq_zero,
    nth_rewrite 0 mij_conj,
    rw complex.conj_im,
    rw add_left_neg
  },

  rw eq_comm at mij_conj,
  rw mij_re,
  refl,
end

-- The sum of a matrix and its conjugate is a real matrix 
lemma matrix_conj_add_real (M : matrix n n ℂ) : ∃ N : matrix n n ℝ , (matrix_conj M + M) = N :=
begin
  rw matrix_eq_conj_iff_real,
  rw mat_add_conj,
  rw matrix_conj_conj,
  rw add_comm, 
end

section hermitian

-- A matrix is called Hermitian if it is equal to the conjugate of its transpose 
def is_hermitian (M : matrix n n ℂ) :=  matrix_conj Mᵀ  = M

-- The sum of two Hermitian matrices is Hermitian
lemma herm_sum (M : matrix n n ℂ) (N : matrix n n ℂ) (hm : is_hermitian M) (hn : is_hermitian N) : is_hermitian (M + N) :=
begin
  rw is_hermitian,
  rw is_hermitian at hm,
  rw is_hermitian at hn,
  funext,
  rw matrix_conj,
  dsimp,
  rw vector_conj,
  dsimp,
  nth_rewrite 1 ← hm,
  nth_rewrite 1 ← hn,
  repeat {rw matrix_trans_conj},
  dsimp,
  repeat {rw matrix_conj},
  dsimp,
  repeat {rw vector_conj},
  dsimp,
  rw map_add,
end

-- A Hermitian matrix only has real eigenvalues
theorem hermitian_real_eigenvalues (M : matrix n n ℂ) (h : is_hermitian M) (e : ℂ) (ev : has_eigenvalue M e) : e.im = 0 :=
begin
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases ep with nz mul,
  rw is_hermitian at h,

  have mul_0 : dot_product (vector_conj v) (M.mul_vec v) = dot_product (vector_conj v) (e • v), 
  {
    rw mul,
  },

  have mul_1 : dot_product (vector_conj v) (e • v) = e * (vector_sq_mag v),
  {
    rw vector_sq_mag,
    simp only [dot_product_smul, algebra.id.smul_eq_mul],
  },

  have mul_2 : dot_product v (e • (vector_conj v)) = e * vector_sq_mag v,
  {
    rw dot_product_comm,
    rw vector_sq_mag,
    rw dot_product,
    rw dot_product,
    rw finset.mul_sum,
    rw finset.sum_congr,
    refl,
    intros _ _,
    simp only [pi.smul_apply, algebra.id.smul_eq_mul,mul_assoc],
  },

  have mul_3 : dot_product (vector_conj v) (mul_vec (Mᵀ.matrix_conj) v) = (conj e) * vector_sq_mag v,
  {
    rw dot_product_mul_vec,
    rw matrix_trans_conj,
    rw vec_mul_trans,
    rw ← mul_vec_conj,
    rw mul,
    rw vec_smul_conj,
    rw vector_sq_mag,
    simp only [smul_dot_product, algebra.id.smul_eq_mul],
  },

  rw h at mul_3,
  rw mul at mul_3,
  rw mul_1 at mul_3,
  rw ne at nz,
  rw ← vector_zero_iff_sq_mag_zero at nz,
  rw vector_sq_mag at nz,
  rw ← vector_sq_mag at nz,
  rw mul_eq_mul_right_iff at mul_3,
  simp only [nz] at mul_3,
  rw or_false at mul_3,
  
  have e_im := congr_arg complex.im mul_3,
  
  rw complex.conj_im at e_im,
  rw eq_neg_iff_add_eq_zero at e_im,
  rw add_self_eq_zero at e_im,
  exact e_im,
end

-- M is Hermitian iff -M is Hermitian
theorem herm_iff_neg_herm (M : matrix n n ℂ) : is_hermitian M ↔ is_hermitian (-M) :=
begin
  repeat {rw is_hermitian},
  
  have key : (-M)ᵀ.matrix_conj = -(Mᵀ.matrix_conj),
  {
    funext,
    rw matrix_conj,
    rw matrix_conj,
    dsimp,
    rw vector_conj,
    rw vector_conj,
    dsimp,
    ext,
    simp only [complex.neg_re, complex.conj_re],
    simp only [complex.neg_im, complex.conj_im]
  },

  rw key,
  rw neg_inj,
end

-- A Hermitian matrix multiplied by a non-zero real number is Hermitian
theorem herm_real_smul_herm (M : matrix n n ℂ) (a : ℂ) : a=a.re → (a=0 ∨ is_hermitian M ↔ is_hermitian (a • M)):=
begin
  intro a_re,
  rw is_hermitian,
  rw is_hermitian,
  rw transpose_smul,
  rw mat_smul_conj Mᵀ a,
  nth_rewrite 1 a_re,
  simp only [is_R_or_C.conj_of_real, complex.coe_smul],
  split,
  intro h,
  cases h with az m_herm,
  rw az,
  rw zero_smul,
  rw complex.zero_re,
  rw zero_smul,
  rw m_herm,
  rw a_re,
  simp only [complex.of_real_re, complex.coe_smul],
  intro h,
  rw or_iff_not_and_not,
  by_contra h_1,
  cases h_1 with anz mnh,
  apply mnh,
  rw ← sub_eq_zero at h,
  rw a_re at h,
  simp only [complex.of_real_re, complex.coe_smul] at h,
  rw ← smul_sub at h,
  rw smul_eq_zero at h,
  rw a_re at anz,
  rw complex.of_real_eq_zero at anz,
  simp only [anz, false_or] at h,
  rw sub_eq_zero at h,
  exact h,
end

-- Every matrix can be written in the form A + iB, where A and B are Hermitian matrices
theorem matrix_decomposition_hermitian (M : matrix n n ℂ) : ∃ A : matrix n n ℂ, ∃ B : matrix n n ℂ, is_hermitian A ∧ is_hermitian B ∧ M = A + complex.I • B :=
begin
  have h := herm_real_smul_herm, 

  have trivial : (1/2) = ((complex.re(1/2)):ℂ),
  {
    ext,
    rw complex.of_real_re,
    rw complex.of_real_im,
    simp only [one_div, complex.inv_im, complex.bit0_im, complex.one_im, bit0_zero, neg_zero', zero_div],
  },

  have trivial_2 : ((1:ℂ)/2) = 0 = false,
  {
    simp only [eq_iff_iff, iff_false],
    by_contra,
    simp only [one_div, inv_eq_zero, bit0_eq_zero, one_ne_zero] at h,
    exact h,
  },

  have trivial_3 : (1:ℂ)/2 + (1:ℂ)/2 = 1,
  {
    rw ← sub_eq_zero,
    rw ← two_mul,
    rw mul_div_comm,
    rw div_self,
    rw mul_one,
    rw sub_self,
    by_contra,
    rw ← one_add_one_eq_two at h,
    rw add_self_eq_zero at h,
    
    have h_1 := one_ne_zero,
    
    rw ne at h_1,
    apply h_1,
    exact h,
    exact infinite.nontrivial ℂ,
  },

  use ((1:ℂ)/2) • (M + (matrix_conj Mᵀ)),
  use (complex.I/2) • ((matrix_conj Mᵀ) - M),

  split,
  rw ← herm_real_smul_herm,
  rw trivial_2,
  rw false_or,
  rw is_hermitian,
  rw transpose_add,
  rw mat_add_conj,
  nth_rewrite 1 add_comm,
  rw add_left_cancel_iff,
  rw matrix_trans_conj,
  rw matrix_conj_conj,
  rw transpose_transpose,
  exact trivial,
  split,
  
  rw is_hermitian,
  rw smul_sub,
  rw matrix_trans_conj,
  rw mat_sub_conj,
  rw matrix_trans_conj,
  rw mat_smul_conj,
  simp only [transpose_sub, transpose_smul],
  rw matrix_trans_conj,
  rw transpose_transpose,
  rw matrix_conj_conj,

  have conj_i : conj(complex.I/2) = -complex.I/2,
  {
    ext,
    rw complex.conj_re,
    rw neg_div,
    rw complex.neg_re,
    rw eq_neg_iff_add_eq_zero,
    rw add_self_eq_zero,
    rw complex.div_re,
    rw complex.I_re,
    simp only [zero_mul, zero_div, complex.bit0_im, complex.one_im, bit0_zero, mul_zero, add_zero],
    rw complex.conj_im,
    rw neg_div,
    rw complex.neg_im,
  },

  rw conj_i,
  rw neg_div,
  nth_rewrite 1 ← neg_add_eq_sub,
  rw neg_smul,
  rw sub_eq_add_neg,
  rw add_right_inj,
  rw mat_smul_conj,
  rw conj_i,
  rw transpose_smul,
  rw neg_div,
  rw neg_smul,
  rw neg_neg,

  rw smul_add,
  rw ← smul_assoc,
  rw smul_sub,
  rw smul_eq_mul,
  rw mul_div,
  rw complex.I_mul_I,
  rw neg_div,
  rw neg_smul,
  rw neg_smul,
  rw neg_sub_neg,
  rw add_add_sub_cancel,
  rw ← add_smul,
  rw trivial_3,
  rw one_smul,
  exact n,
  exact _inst_1,
  exact _inst_3,
end

-- Every Hermitian matrix can be written as A + iB, where A is a symmetric real matrix and B is a skew-symmetric real matrix
theorem matrix_decomposition_symm_skew_symm (M : matrix n n ℂ) (herm : is_hermitian M) : ∃ A : matrix n n ℝ , ∃ B : matrix n n ℝ, is_symm A ∧ is_skew_symmetric B ∧ M = A + complex.I • B:=
begin

  have mul_2_scal: ∀ (x y : ℂ) , x = y ↔ (2 : ℂ)*x = (2 : ℂ)*y,
  {
    intros x y,
    split,
    intro xey,
    rw xey,

    intro xey_2,

    rw mul_eq_mul_left_iff at xey_2,
    cases xey_2 with xey f,
    exact xey,
    exfalso,
    rw ← one_add_one_eq_two at f,
    rw add_self_eq_zero at f,
    
    have onz := one_ne_zero,

    rw ne at onz,
    apply onz,
    exact f,
    exact infinite.nontrivial ℂ,
  },  

  have mul_2 : ∀ (X Y : matrix n n ℂ) , X = Y ↔ (2 : ℂ) • X = (2 : ℂ) • Y,
  {
    intros X Y,
    split,
    intro xey,
    rw xey,
    intro xey_2,
    funext,
    repeat{rw two_smul at xey_2},
    
    have mul_2_scalar : (X + X) x x_1 = (Y+Y) x x_1,
    {rw xey_2},

    simp only [dmatrix.add_apply] at mul_2_scalar,
    repeat {rw ← two_mul at mul_2_scalar},
    rw mul_eq_mul_left_iff at mul_2_scalar,
    simp only [bit0_eq_zero, one_ne_zero, or_false] at mul_2_scalar,
    exact mul_2_scalar,
  },

  have complex_two_nez : (2:ℂ) ≠ (0:ℂ),
  {
    rw ← one_add_one_eq_two,
    rw ne.def,
    rw add_self_eq_zero,
    rw ← ne.def,
    exact one_ne_zero,
  },

  have two_inv_real : (2:ℂ)⁻¹.re = (2:ℝ)⁻¹,
  {
    simp only [complex.inv_re, complex.bit0_re, complex.one_re],
    rw eq_comm,
    apply eq_div_of_mul_eq,
    simp only [ne.def, monoid_with_zero_hom.map_eq_zero, bit0_eq_zero, one_ne_zero, not_false_iff],
    rw complex.norm_sq,
    dsimp,
    simp only [complex.bit0_im, complex.one_im, bit0_zero, mul_zero, add_zero, inv_mul_cancel_left₀, ne.def, bit0_eq_zero,
    one_ne_zero, not_false_iff],
  },

  have two_inv_im : (2:ℂ)⁻¹.im = (0:ℝ),
  {
    rw complex.inv_im,
    simp only [complex.bit0_im, complex.one_im, bit0_zero, neg_zero', zero_div],
  },

  have h_1 : ((1:ℂ)/2) • (matrix_conj M + M) = matrix_conj (((1:ℂ)/2) • (matrix_conj M + M)),
  { 
    rw mat_smul_conj, 
    rw mat_add_conj,
    rw matrix_conj_conj,
    rw add_comm,
    
    suffices c12 : (1:ℂ)/2 = conj ((1:ℂ)/2),
    {rw ← c12},

    rw one_div,
    rw eq_comm,
    rw complex.eq_conj_iff_im,
    exact two_inv_im,
  },

  have conj_i : conj(complex.I/2) = -complex.I/2,
  {
    ext,
    rw complex.conj_re,
    rw neg_div,
    rw complex.neg_re,
    rw eq_neg_iff_add_eq_zero,
    rw add_self_eq_zero,
    rw complex.div_re,
    rw complex.I_re,
    simp only [zero_mul, zero_div, complex.bit0_im, complex.one_im, bit0_zero, mul_zero, add_zero],
    rw complex.conj_im,
    rw neg_div,
    rw complex.neg_im,
  },

  have g_1 : (complex.I/(2:ℂ)) • (matrix_conj M - M) = matrix_conj ((complex.I/(2:ℂ)) • (matrix_conj M - M)),
  {
    rw mat_smul_conj,
    rw mat_sub_conj,
    rw matrix_conj_conj,
    simp_rw smul_sub,
    rw conj_i,
    repeat {rw neg_div},
    repeat {rw neg_smul},
    rw neg_sub_neg,
  },

  rw ← matrix_eq_conj_iff_real at h_1,
  cases h_1 with N hN,
  rw ← matrix_eq_conj_iff_real at g_1,
  cases g_1 with O hO, 
  
  existsi N,
  existsi O,
  rw is_hermitian at herm, 

  split,
  
  rw is_symm, 

  have h_2 : Nᵀ = N,
  {
    ext,
    rw ← complex.of_real_inj,
    
    have h_3 : ∀ (i_1 i_2 : n ), (N:matrix n n ℂ) i_1 i_2 = ((N i_1 i_2):ℂ),
    intros i_1 i_2,
    refl,

    have n_ji : (N:matrix n n ℂ) j i = ((N j i):ℂ),
    specialize h_3 j i,
    rw h_3,

    have n_ij : (N:matrix n n ℂ) i j = ((N i j):ℂ),
    specialize h_3 i j,
    rw h_3,

    rw ← n_ji,
    rw ← n_ij,

    rw ← hN,
    dsimp,
    nth_rewrite 0 ← herm,
    rw matrix_conj_conj,
    rw transpose,
    nth_rewrite 2 ← herm,
    rw matrix_conj_conj,
    rw transpose,
    rw add_comm,
  },

  have mul_3 := mul_2,

  specialize mul_2 M,
  specialize mul_2 (↑(((1:ℝ) / 2) • N) + -(((1:ℂ) / 2) • M.matrix_conj) + ((1:ℂ) / 2) • M),

  have n_smul : (N:(matrix n n ℂ)) = (2:ℂ) • ( ((1:ℂ)/2) • (N:(matrix n n ℂ))),
  {simp only [one_div, smul_inv_smul₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff]},

  rw h_2,

  have g_3 : Oᵀ = -O,
  {
    ext,
    rw transpose_apply,
    repeat{rw pi.neg_apply},
    rw ← complex.of_real_inj,
    rw complex.of_real_neg,

    have h_3 : ∀ (i_1 i_2 : n ), (O:matrix n n ℂ) i_1 i_2 = ((O i_1 i_2):ℂ),
    intros i_1 i_2,
    refl,

    have o_ji : (O:matrix n n ℂ) j i = ((O j i):ℂ),
    specialize h_3 j i,
    rw h_3,

    have o_ij : (O:matrix n n ℂ) i j = ((O i j):ℂ),
    specialize h_3 i j,
    rw h_3,

    rw ← o_ji,
    rw ← o_ij,
    repeat {rw ← hO},

    simp only [pi.smul_apply, pi.sub_apply, algebra.id.smul_eq_mul],
    repeat {rw mul_sub},
    rw neg_sub,
    nth_rewrite 0 ← herm,
    nth_rewrite 3 ← herm,
    repeat {rw matrix_conj_conj},
    repeat {rw transpose_apply}, 
  },

  split,
  rw is_skew_symmetric,
  rw g_3,
  rw ← hO,
  rw ← hN,
  rw smul_add,
  rw ← smul_assoc,
  rw smul_eq_mul,
  rw ← mul_div_assoc,
  rw complex.I_mul_I,
  rw neg_div,
  rw smul_sub,
  simp only [one_div, neg_smul, neg_sub_neg],
  rw add_sub,
  rw add_assoc,
  rw add_sub_cancel',
  rw mul_2,
  simp only [smul_add, smul_inv_smul₀, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff],
  rw ← one_add_one_eq_two,
  rw add_smul,
  repeat {rw one_smul},
end

-- A Hermitian real matrix is symmetric
lemma hermitian_real_symm  (M : matrix n n ℝ) (herm : is_hermitian (M:matrix n n ℂ)) : M.is_symm:=
begin
  rw is_hermitian at herm,
  rw is_symm,
  
  have herm_1 : ∀ (i j : n), ((M : matrix n n ℂ)ᵀ.matrix_conj) i j = M i j,
  {
    intros i j,
    rw herm,
    refl
  },

  funext i j,
  specialize herm_1 i j,
  rw matrix_trans_conj at herm_1,
  rw transpose_apply at herm_1,
  rw matrix_conj at herm_1,
  simp_rw vector_conj at herm_1,
  
  unfold coe at herm_1,
  unfold lift_t at herm_1,
  unfold has_lift_t.lift at herm_1,
  unfold coe_t at herm_1,
  unfold has_coe_t.coe at herm_1,
  unfold coe_b at herm_1,
  unfold has_coe.coe at herm_1,
  
  have trivial : ((conj (({re := M j i, im := 0}):ℂ)):ℂ) = (({re := M j i, im := 0}):ℂ),
  {
    ext,
    rw complex.conj_re,
    rw complex.conj_im,
    unfold complex.im,
    rw neg_zero'
  },

  rw trivial at herm_1,
  rw transpose_apply,
  
  have trivial_re := congr_arg complex.re herm_1,
  
  unfold complex.re at trivial_re,
  exact trivial_re,
end

section definite

-- A Hermitian matrix is called positive definite if the product vᵀMv is greater than 0 for all non-zero vectors v 
def is_pos_def (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 < dot_product (vector_conj v) (M.mul_vec v)

-- A Hermitian matrix is called negative definite if the product vᵀMv is smaller than 0 for all non-zero vectors v
def is_neg_def (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 > dot_product (vector_conj v) (M.mul_vec v) 

-- A Hermitian matrix is called positive semidefinite if the product vᵀMv is greater than or equal to 0 for all non-zero vectors v
def is_pos_semidef (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 ≤ dot_product (vector_conj v) (M.mul_vec v)

-- -- A Hermitian matrix is called negative semidefinite if the product vᵀMv is greater than 0 for all non-zero vectors v
def is_neg_semidef (M : matrix n n ℂ) := M.is_hermitian ∧ ∀ (v : n → ℂ), v ≠ 0 → 0 ≥ dot_product (vector_conj v) (M.mul_vec v) 

-- A positive definite matrix only has positive eigenvalues
theorem pos_def_pos_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_pos_def) (ev : has_eigenvalue M e) : e > 0 := 
begin
  rw is_pos_def at h,
  
  have ev_prop := ev,
  
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases h with herm mul,
  
  have herm_prop := herm,
  
  rw is_hermitian at herm,
  cases ep with vnz vmul,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  rw vmul at mul,
  rw dot_product_smul at mul,
  rw ← vector_sq_mag at mul,
  rw smul_eq_mul at mul,
  
  have vmgz : vector_sq_mag v > 0,
  {
    rw gt_iff_lt,
    rw lt_iff_le_and_ne,
    split,
    rw ← ge_iff_le,
    simp only [vector_sq_mag_geq_zero],
    rw ne.def,
    rw eq_comm,
    rw vector_zero_iff_sq_mag_zero,
    rw ← ne.def,
    exact vnz
  },

  rw vector_sq_mag_real at mul,
  rw vector_sq_mag_real at vmgz,
  
  have e_re : e = e.re,
  
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  apply hermitian_real_eigenvalues M herm_prop e,
  exact ev_prop,
  rw e_re at mul,
  rw e_re,

  have key : 0 < (e.re) * ((vector_sq_mag v).re) / ((vector_sq_mag v).re),
  {  
    apply div_pos,
    cases mul with mul_re mul_im,
    simp only [complex.zero_re, complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero] at mul_re,
    exact mul_re,
    rw ← gt_iff_lt,
    simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
    rwa gt_iff_lt
  },

  rw mul_div_cancel at key,
  simp only [key, gt_iff_lt, complex.zero_lt_real],
  rw ne.def,
  by_contra vz,
  rw vz at vmgz,
  simp only [complex.of_real_zero, gt_iff_lt, lt_self_iff_false] at vmgz,
  exact vmgz,
end

-- A positive semidefinite matrix only has nonnegative eigenvalues
theorem pos_semidef_nonneg_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_pos_semidef) (ev : has_eigenvalue M e) : e ≥ 0 := 
begin
  rw is_pos_semidef at h,
  
  have ev_prop := ev,
  
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases h with herm mul,
  
  have herm_prop := herm,
  
  rw is_hermitian at herm,
  cases ep with vnz vmul,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  rw vmul at mul,
  rw dot_product_smul at mul,
  rw ← vector_sq_mag at mul,
  rw smul_eq_mul at mul,
  
  have vmgz : vector_sq_mag v > 0,
  {
    rw gt_iff_lt,
    rw lt_iff_le_and_ne,
    split,
    rw ← ge_iff_le,
    simp only [vector_sq_mag_geq_zero],
    rw ne.def,
    rw eq_comm,
    rw vector_zero_iff_sq_mag_zero,
    rw ← ne.def,
    exact vnz
  },

  rw vector_sq_mag_real at mul,
  rw vector_sq_mag_real at vmgz,
  
  have e_re : e = e.re,
  {
    ext,
    rw complex.of_real_re,
    rw complex.of_real_im,
    apply hermitian_real_eigenvalues M herm_prop e,
    exact ev_prop
  },

  rw e_re at mul,
  rw e_re,
  
  have key : 0 ≤ (e.re) * ((vector_sq_mag v).re) / ((vector_sq_mag v).re),
  {
    apply div_nonneg,
    cases mul with mul_re mul_im,
    simp only [complex.zero_re, complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero] at mul_re,
    exact mul_re,
    rw ← ge_iff_le,
    simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
    rw ge_iff_le,
    rw lt_iff_le_and_ne at vmgz,
    cases vmgz with vge vne,
    exact vge
  },

  rw mul_div_cancel at key,
  simp only [key, ge_iff_le, complex.zero_le_real],
  rw ne.def,
  by_contra vz,
  rw vz at vmgz,
  simp only [complex.of_real_zero, gt_iff_lt, lt_self_iff_false] at vmgz,
  exact vmgz,
end

-- M is negative definite iff -M is positive definite
theorem neg_def_iff_neg_pos_def (M : matrix n n ℂ) : is_neg_def M ↔ is_pos_def (-M) :=
begin

  have important : ∀ v : n → ℂ ,  dot_product (vector_conj v) ((-M).mul_vec v) = -dot_product (vector_conj v) (M.mul_vec v),
  {
    intro v,
    rw dot_product,
    rw dot_product,
    rw ← finset.sum_neg_distrib,
    rw finset.sum_congr,
    refl,
    intros _ _,
    rw neg_mul_vec,
    rw pi.neg_apply,
    rw mul_neg
  },

  rw is_neg_def,
  rw is_pos_def,
  rw ← herm_iff_neg_herm,
  rw and.congr_right_iff,
  intro herm,
  
  split;
  
  intro prop;
  intro v;
  intro vnz;
  specialize prop v;
  simp only [vnz, ne.def, not_false_iff, forall_true_left, gt_iff_lt] at prop;
  specialize important v,
  rw important,
  simp only [prop, right.neg_pos_iff],
  rw important at prop,
  rw right.neg_pos_iff at prop,
  rw gt_iff_lt,
  exact prop,
end 

-- M is negative semidefinite iff -M is positive semidefinite
theorem neg_semidef_iff_neg_pos_semidef (M : matrix n n ℂ) : is_neg_semidef M ↔ is_pos_semidef (-M) :=
begin

  have important : ∀ v : n → ℂ ,  dot_product (vector_conj v) ((-M).mul_vec v) = -dot_product (vector_conj v) (M.mul_vec v),
  {
    intro v,
    rw dot_product,
    rw dot_product,
    rw ← finset.sum_neg_distrib,
    rw finset.sum_congr,
    refl,
    intros _ _,
    rw neg_mul_vec,
    rw pi.neg_apply,
    rw mul_neg
  },

  rw is_neg_semidef,
  rw is_pos_semidef,
  rw ← herm_iff_neg_herm,
  rw and.congr_right_iff,
  intro herm,
  
  split;
  
  intro prop;
  intro v;
  intro vnz;
  specialize prop v;
  simp only [vnz, ne.def, not_false_iff, forall_true_left, gt_iff_lt] at prop;
  specialize important v,
  rw important,
  simp only [right.nonneg_neg_iff],
  rwa ← ge_iff_le,
  rw important at prop,
  rw right.nonneg_neg_iff at prop,
  exact prop,
end 

-- A negative definite matrix only has negative eigenvalues
theorem neg_def_neg_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_neg_def) (ev : has_eigenvalue M e) : e < 0 := 
begin
  rw neg_def_iff_neg_pos_def at h,
  
  have ev_prop := ev,
  
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases ep with vnz vmul,
  rw is_pos_def at h,
  cases h with herm_prop mul,
  rw ← herm_iff_neg_herm at herm_prop,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  
  have neg_vmul : (-M).mul_vec v = -(e • v),
  
  rw neg_mul_vec,
  rw neg_inj,
  exact vmul,
  rw neg_vmul at mul,
  simp only [dot_product_neg, dot_product_smul, algebra.id.smul_eq_mul, right.neg_pos_iff] at mul,
  rw ← vector_sq_mag at mul,

  have vmgz : vector_sq_mag v > 0,
  {
    rw gt_iff_lt,
    rw lt_iff_le_and_ne,
    split,
    rw ← ge_iff_le,
    simp only [vector_sq_mag_geq_zero],
    rw ne.def,
    rw eq_comm,
    rw vector_zero_iff_sq_mag_zero,
    rw ← ne.def,
    exact vnz
  },

  rw vector_sq_mag_real at mul,
  rw vector_sq_mag_real at vmgz,
  
  have e_re : e = e.re,
  
  ext,
  rw complex.of_real_re,
  rw complex.of_real_im,
  apply hermitian_real_eigenvalues M herm_prop e,
  exact ev_prop,
  rw e_re at mul,
  rw e_re,
  
  have key : (e.re) * ((vector_sq_mag v).re) / ((vector_sq_mag v).re) < 0,
  {
    rw div_neg_iff,
    cases mul with mul_re mul_im,
    simp only [complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero, complex.zero_re] at mul_re,
    simp only,
    right,
    split,
    exact mul_re,
    simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
    exact vmgz
  },

  rw mul_div_cancel at key,
  rw complex.lt_def,
  split,
  simp only [key, complex.of_real_re, complex.zero_re],
  simp only [complex.of_real_im, complex.zero_im],
  rw ne_iff_lt_or_gt,
  right,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  rwa gt_iff_lt, 
end

-- A negative semidefinite matrix only has nonpositive eigenvalues
theorem neg_semidef_nonpos_eigenvalues (M : matrix n n ℂ) (e : ℂ) (h : M.is_neg_semidef) (ev : has_eigenvalue M e) : e ≤ 0 := 
begin
  rw neg_semidef_iff_neg_pos_semidef at h,
  
  have ev_prop := ev,
  
  rw has_eigenvalue at ev,
  cases ev with v ep,
  rw has_eigenpair at ep,
  cases ep with vnz vmul,
  rw is_pos_semidef at h,
  cases h with herm_prop mul,
  rw ← herm_iff_neg_herm at herm_prop,
  specialize mul v,
  simp only [vnz, ne.def, not_false_iff, forall_true_left] at mul,
  
  have neg_vmul : (-M).mul_vec v = -(e • v),
  
  rw neg_mul_vec,
  rw neg_inj,
  exact vmul,
  rw neg_vmul at mul,
  simp only [dot_product_neg, dot_product_smul, algebra.id.smul_eq_mul, right.neg_pos_iff] at mul,
  rw ← vector_sq_mag at mul,

  have vmgz : vector_sq_mag v > 0,
  {
    rw gt_iff_lt,
    rw lt_iff_le_and_ne,
    split,
    rw ← ge_iff_le,
    simp only [vector_sq_mag_geq_zero],
    rw ne.def,
    rw eq_comm,
    rw vector_zero_iff_sq_mag_zero,
    rw ← ne.def,
    exact vnz
  },

  rw vector_sq_mag_real at mul,
  rw vector_sq_mag_real at vmgz,
  
  have e_re : e = e.re,
  {
    ext,
    rw complex.of_real_re,
    rw complex.of_real_im,
    apply hermitian_real_eigenvalues M herm_prop e,
    exact ev_prop
  },

  rw e_re at mul,
  rw e_re,
  
  have key : (e.re) * ((vector_sq_mag v).re) / ((vector_sq_mag v).re) ≤ 0,
  {
    rw div_nonpos_iff,
    cases mul with mul_re mul_im,
    simp only [complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero, complex.zero_re] at mul_re,
    simp only,
    right,
    split,
    simp only [complex.neg_re, complex.mul_re, complex.of_real_re, complex.of_real_im, mul_zero, sub_zero, right.nonneg_neg_iff] at mul_re,
    exact mul_re,
    simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
    rw lt_iff_le_and_ne at vmgz,
    cases vmgz with vmge vne,
    exact vmge
  },

  rw mul_div_cancel at key,
  rw complex.le_def,
  split,
  simp only [key, complex.of_real_re, complex.zero_re],
  simp only [complex.of_real_im, complex.zero_im],
  rw ne_iff_lt_or_gt,
  right,
  simp only [gt_iff_lt, complex.zero_lt_real] at vmgz,
  rwa gt_iff_lt, 
end

-- The sum of a positive definite matrix and a positive semidefinite matrix is positive definite
theorem pos_def_add_semidef_pos (M N : matrix n n ℂ) (hm : is_pos_def M) (hn : is_pos_semidef N) : is_pos_def (M + N) :=
begin
  rw is_pos_def,
  rw is_pos_def at hm,
  rw is_pos_semidef at hn,
  cases hm with herm_m eq_m,
  cases hn with herm_n eq_n,
  split,
  exact herm_sum M N herm_m herm_n,

  intros v vnz,
  specialize eq_m v vnz,
  specialize eq_n v vnz,
  rw matrix.add_mul_vec,
  rw dot_product_add,
  
  have trivial : ∀ (x y : ℂ), 0 < x → 0 ≤ y → 0 < x + y,
  {
    intros x y hx hy, 
    rw complex.lt_def at hx,
    cases hx with hx_re hx_im, 
    rw complex.le_def at hy,
    cases hy with hy_re hy_im,
    rw complex.lt_def,
    
    split,

    rw complex.add_re,
    rw complex.zero_re,
    rw complex.zero_re at hx_re hy_re,
    nlinarith,

    rw complex.add_im,
    rw complex.zero_im,
    rw complex.zero_im at hx_im hy_im,
    nlinarith,
  },

  exact trivial (vector_conj v ⬝ᵥ M.mul_vec v) (vector_conj v ⬝ᵥ N.mul_vec v) eq_m eq_n,   
end

-- The sum of two positive semidefinite matrices is positive semidefinite
theorem pos_semidef_add_semidef_semidef (M N : matrix n n ℂ) (hm : is_pos_semidef M) (hn : is_pos_semidef N) : is_pos_semidef (M + N) :=
begin
  rw is_pos_semidef,
  rw is_pos_semidef at hm hn,
  cases hm with herm_m eq_m,
  cases hn with herm_n eq_n,
  split,
  exact herm_sum M N herm_m herm_n,

  intros v vnz,
  specialize eq_m v vnz,
  specialize eq_n v vnz,
  rw matrix.add_mul_vec,
  rw dot_product_add,
  
  have add := add_le_add eq_m eq_n,
  rw zero_add at add,

  exact add,   
end

-- The sum of a negative definite matrix and a negative semidefinite matrix is negative definite
theorem neg_add_semineg_neg (M N : matrix n n ℂ) (hm : is_neg_def M) (hn : is_neg_semidef N) : is_neg_def (M + N) :=
begin
  rw is_neg_def,
  rw is_neg_def at hm,
  rw is_neg_semidef at hn,
  cases hm with herm_m eq_m,
  cases hn with herm_n eq_n,
  split,
  exact herm_sum M N herm_m herm_n,

  intros v vnz,
  specialize eq_m v vnz,
  specialize eq_n v vnz,
  rw matrix.add_mul_vec,
  rw dot_product_add,
  
  have trivial : ∀ (x y : ℂ), x < 0 → y ≤ 0 → x + y < 0,
  {
    intros x y hx hy, 
    rw complex.lt_def at hx,
    cases hx with hx_re hx_im, 
    rw complex.le_def at hy,
    cases hy with hy_re hy_im,
    rw complex.lt_def,
    
    split,

    rw complex.add_re,
    rw complex.zero_re,
    rw complex.zero_re at hx_re hy_re,
    nlinarith,

    rw complex.add_im,
    rw complex.zero_im,
    rw complex.zero_im at hx_im hy_im,
    nlinarith,
  },

  rw gt_iff_lt at eq_m,
  rw ge_iff_le at eq_n,
  rw gt_iff_lt,

  exact trivial (vector_conj v ⬝ᵥ M.mul_vec v) (vector_conj v ⬝ᵥ N.mul_vec v) eq_m eq_n,   
end

-- The sum of two positive semidefinite matrices is positive semidefinite
theorem neg_semidef_add_semidef_semidef (M N : matrix n n ℂ) (hm : is_neg_semidef M) (hn : is_neg_semidef N) : is_neg_semidef (M + N) :=
begin
  rw is_neg_semidef,
  rw is_neg_semidef at hm hn,
  cases hm with herm_m eq_m,
  cases hn with herm_n eq_n,
  split,
  exact herm_sum M N herm_m herm_n,

  intros v vnz,
  specialize eq_m v vnz,
  specialize eq_n v vnz,
  rw matrix.add_mul_vec,
  rw dot_product_add,
  
  have add := add_le_add eq_m eq_n,
  rw zero_add at add,

  exact add,   
end

end definite

end hermitian

-- Any two eigenvectors corresponding to different eigenvalues are linearly independent
lemma eigenvectors_linearly_independent (M : matrix n n ℂ) (u v : n → ℂ) (e r : ℂ)
(ep_1 : has_eigenpair M e u) (ep_2 : has_eigenpair M r v) (neq : e ≠ r) :
∀ (a b : ℂ), a • u + b • v = 0 → a = 0 ∧ b = 0 :=
begin
  intros a b lcz,
  rw has_eigenpair at ep_1 ep_2,
  cases ep_1 with unz ep_1,
  cases ep_2 with vnz ep_2,
  
  rw ne at neq vnz unz,

  have mlcz := congr_arg M.mul_vec lcz,

  rw mul_vec_add at mlcz,
  repeat {rw mul_vec_smul at mlcz},
  rw ep_1 at mlcz,
  rw ep_2 at mlcz,
  rw mul_vec_zero at mlcz,

  have elcz := congr_arg (λ x, e • x) lcz,
  
  dsimp at elcz,
  rw smul_add at elcz,
  rw smul_zero at elcz,
  rw smul_comm at elcz,
  rw ← elcz at mlcz,
  rw add_right_inj at mlcz,
  rw smul_comm at mlcz,

  have key : (r - e) • b • v = 0,
  {
    rw sub_smul,
    rw mlcz,
    rw sub_self,
  },

  rw smul_eq_zero at key,
  cases key with emrz key,
  exfalso,
  apply neq,
  rw sub_eq_zero at emrz,
  rw eq_comm,
  exact emrz,
  rw smul_eq_zero at key,
  rw or_comm at key,
  cases key with vz bz,
  exfalso,
  apply vnz,
  exact vz,
  split,
  swap,
  exact bz,
  rw bz at lcz,
  simp only [zero_smul, add_zero, smul_eq_zero] at lcz,
  cases lcz with az uz,
  exact az,
  exfalso,
  apply unz,
  exact uz,
end   

-- Any linear combination (with non-zero coefficients) of two eigenvectors corresponding to different eigenvalues is not an eigenvector
theorem independent_eigenvectors_linear_combination_not_eigenvector (M : matrix n n ℂ) (u v : n → ℂ) (e r : ℂ) (neq : e ≠ r)
(ep_1 : has_eigenpair M e u) (ep_2 : has_eigenpair M r v) : ∀ (a b : ℂ), a ≠ 0 → b ≠ 0 → ¬(has_eigenvector M (a•u+b•v)) :=
begin
  have epeu := ep_1,
  have eprv := ep_2,
  
  intros a b anz bnz,
  rw ne at anz bnz neq,
  by_contra ev,
  rw has_eigenvector at ev,
  cases ev with t ep,
  rw has_eigenpair at ep,
  cases ep with lc mul,
  rw mul_vec_add at mul,
  rw smul_add at mul,
  repeat {rw mul_vec_smul at mul},

  rw has_eigenpair at ep_1 ep_2,
  cases ep_1 with unz mul_1,
  cases ep_2 with vnz mul_2,
  rw ne at unz vnz,
  
  rw [mul_1,mul_2] at mul,

  have helper_lemma : a • (e - t) • u + b • (r - t) • v = 0,
  {
    repeat {rw sub_smul},
    repeat {rw smul_sub},
    rw sub_add_sub_comm,
    rw sub_eq_zero,
    rw smul_comm a t,
    rw smul_comm b t,
    exact mul,
    apply_instance,
    apply_instance
  },

  have lin_ind := eigenvectors_linearly_independent M u v e r epeu eprv neq,
  
  specialize lin_ind (a • (e - t)) (b • (r - t)),

  have ent : ¬(e - t)=0,
  {
    by_contra eeqt,
    rw eeqt at helper_lemma,
    rw [zero_smul, smul_zero, zero_add] at helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma, 
    apply bnz,
    exact helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma,
    rw sub_eq_zero at eeqt helper_lemma,
    apply neq,
    rw [helper_lemma,eeqt],
    apply vnz,
    exact helper_lemma
  },

  have rnt : ¬(r - t) = 0,
  {
    by_contra reqt,
    rw reqt at helper_lemma,
    rw [zero_smul, smul_zero, add_zero] at helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma,
    apply anz,
    exact helper_lemma,
    rw smul_eq_zero at helper_lemma,
    cases helper_lemma,
    apply ent,
    exact helper_lemma,
    apply unz,
    exact helper_lemma
  },

  have aemtnz : a • (e - t) ≠ 0,
  {
    rw smul_ne_zero,
    split,
    rwa ne,
    rwa ne
  },

  have brmtnz : b • (r - t) ≠ 0,
  {
    rw smul_ne_zero,
    split,
    rwa ne,
    rwa ne
  },

  repeat {rw smul_assoc at lin_ind},
  have lin_ind_2 := lin_ind helper_lemma,
  
  repeat {rw smul_assoc at lin_ind_2},
  
  rw ne at aemtnz brmtnz,
  apply aemtnz,
  cases lin_ind_2 with aemtz brmtz,
  exact aemtz,
end

-- If two matrices both have the eigenpair (e,v) then (e * e,v) is an eigenpair of their product
lemma eigenvalue_prod (M : matrix n n ℂ) (N : matrix n n ℂ) 
(v : n → ℂ) (e : ℂ)  (hme : has_eigenpair M e v) (hne : has_eigenpair N e v):
has_eigenpair (M ⬝ N) (e * e) v :=
begin
  cases hme with ve hme,
  cases hne with ve hne,
  rw has_eigenpair,
  split,
  exact ve,
  rw ← mul_vec_mul_vec,
  rw hne,
  rw mul_vec_smul,
  rw hme,
  rw ← smul_assoc,
  rw ← smul_eq_mul,
end

-- (∀ v, u ⬝ v = 0) ↔ u = 0 
lemma forall_left_dot_prod_zero_zero (u : n → ℂ) : (∀ v : (n → ℂ) , dot_product u v = 0) ↔ u = 0:=
begin
  split,
  intro dpz,
  funext,
  specialize dpz (λ i , if i = x then 1 else 0),
  rw dot_product at dpz,
  
  have key : finset.univ.sum (λ (i : n), u i * ite (i = x) 1 0) = finset.univ.sum (λ (i : n), ite (i = x) (u i) 0),
  {
    rw finset.sum_congr,
    refl,
    intros _ _,
    rw mul_ite,
    rw mul_one,
    rw mul_zero,
  },

  rw key at dpz,
  rw finset.sum_ite at dpz,
  simp only [finset.sum_const_zero, add_zero] at dpz,

  have eq_x : (λ (x_1 : n), x_1 = x) = eq x,
  {
    funext,
    rw eq_iff_iff,
    rw eq_comm
  },

  simp_rw eq_x at dpz,

  simp only at dpz,
  rw finset.filter_eq at dpz,
  simp only [finset.mem_univ, if_true, finset.sum_singleton] at dpz,
  rw dpz,
  rw pi.zero_apply,

  intro uz,
  intro v,
  rw uz,
  rw zero_dot_product,
end

-- (∀ v, v ⬝ u = 0) ↔ u = 0
lemma forall_right_dot_prod_zero_zero (u : n → ℂ) : (∀ v : (n → ℂ) , dot_product v u = 0) ↔ u = 0:=
begin
  simp_rw dot_product_comm,
  rw forall_left_dot_prod_zero_zero,
end

-- e is an eigenvalue of M iff det(M - eI)=0
lemma eigenvalue_zero_det (M : matrix n n ℂ) (e : ℂ ) :
has_eigenvalue M e  ↔ ( (M - e • (1 : matrix n n ℂ)).det = 0) :=
begin

  have eigenvector_mul_eq_zero : ∀ (v : n → ℂ), M.mul_vec v = e • v ↔  (M - e • 1).mul_vec v = 0,
  {
    intro v,
    rw sub_mul_vec,
    split,
    intro mul,
    rw mul,
    rw smul_mul_vec_assoc,
    nth_rewrite 0 ← one_mul_vec v,
    rw sub_eq_zero,

    intro sub_zero,
    rw sub_eq_zero at sub_zero,
    rw sub_zero,
    rw smul_mul_vec_assoc,
    rw one_mul_vec,
  },

  rw  ← not_iff_not,
  rw ← ne.def,
  split,
  swap,
  intro dnz,
  by_contra ev,
  rw has_eigenvalue at ev,
  cases ev with v ev,
  rw has_eigenpair at ev,
  cases ev with vnz mul,
  specialize eigenvector_mul_eq_zero v,
  rw eigenvector_mul_eq_zero at mul,
  
  have vec_zero := eq_zero_of_mul_vec_eq_zero dnz mul,
    
  apply vnz,
  exact vec_zero,

  intro n_ev,
  rw has_eigenvalue at n_ev,

  rw ne,
  by_contra,

  have det_t : ((M - e • 1)ᵀ).det = 0,
  {
    rw det_transpose,
    exact h,
  },

  have nn : ¬¬((M - e • 1).det = 0) ↔ (M - e • 1).det = 0,
  {rw not_not},

  rw ← nn at h,

  apply h,
  rw ← ne,

  rw ← nondegenerate_iff_det_ne_zero,
  rw nondegenerate,
  
  intro u,
  intro for_all,

  by_contra unz,

  simp_rw dot_product_mul_vec at for_all,
  rw forall_left_dot_prod_zero_zero at for_all,
  rename for_all vmu,
  
  have dpz := congr_arg (dot_product (vector_conj u)) vmu,

  rw dot_product_zero at dpz,

  have nn_t : ¬¬((M - e • 1)ᵀ.det = 0) ↔ (M - e • 1)ᵀ.det = 0,
  {rw not_not},

  rw ← nn_t at det_t,
  apply det_t, 
  rw ← ne,

  rw ← nondegenerate_iff_det_ne_zero,
  rw nondegenerate,

  intro v,
  intro for_all_t,
  simp_rw dot_product_mul_vec at for_all_t,
  rw forall_left_dot_prod_zero_zero at for_all_t,
  rw vec_mul_trans at for_all_t,
  rw ← eigenvector_mul_eq_zero at for_all_t,
  rw not_exists at n_ev,
  specialize n_ev v,
  by_contra,
  apply n_ev,
  rw has_eigenpair,
  split,
  rwa ne,
  exact for_all_t,
end 

-- The (right) eigenpairs of a matrix are the left eigenpairs of the transpose
theorem eigenpair_left_trans (M : matrix n n ℂ) (v : n → ℂ) (e : ℂ):
has_eigenpair M e v ↔ has_left_eigenpair Mᵀ e v:=
begin
  rw has_eigenpair,
  rw has_left_eigenpair,
  rw vec_mul_trans,
end

-- The eigenvalues and left eigenvalues of a matrix coincide
theorem left_eigenvalue_right_eigenvalue (M : matrix n n ℂ) (e : ℂ):
has_eigenvalue M e ↔ has_left_eigenvalue M e :=
begin

  have left_eigenvalue_trans : has_left_eigenvalue M e ↔ has_eigenvalue Mᵀ e,
  {
    rw has_eigenvalue,
    rw has_left_eigenvalue,
    
    split;
    intro x;
    cases x with v ep;
    use v,
    rw ← transpose_transpose M at ep,
    rw ← eigenpair_left_trans at ep,
    exact ep,
    rw eigenpair_left_trans at ep,
    rw transpose_transpose at ep,
    exact ep,
  },

  nth_rewrite 0 left_eigenvalue_trans,
  repeat {rw eigenvalue_zero_det},
  
  have tr : (Mᵀ - e • 1) = (M - e • 1)ᵀ,
  {simp only [transpose_sub, transpose_smul, transpose_one]},

  rw tr,
  rw det_transpose,
end

end matrix