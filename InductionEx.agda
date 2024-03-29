module InductionEx where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎


+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
    -- inductive step ...
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎


+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

{-
This doesn't work because the 1st and 2nd lines aren't
proven to be equal yet.

+-comm1 : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm1 zero n =
  begin
    zero + n
  ≡⟨⟩
    zero
  ≡⟨ +-identityʳ n ⟩
    n + zero
  ∎
-}


+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
    -- Need the cong to make the expressions identicial
    -- Need sym to flip the definition so that it typechecks
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎


{-
Exercise:

+-finite-|-assoc =

I have no idea how to do this.
-}

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero    n p                          = refl
+-assoc' (suc m) n p   rewrite +-assoc' m n p = refl

-- Commutivity of addition with rewrite:

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero                          = refl
+-identity' (suc m) rewrite +-identity' m = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n                       = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n)
  rewrite +-suc'  m n
        | +-comm' m n
  = refl


-- Done interactively:
-- SPC-m-l - load
-- SPC-m-f - next
-- SPC-m-, - goal-and-context
-- SPC-m-r - refine
+-associ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-associ zero n p                           = refl
+-associ (suc m) n p rewrite +-associ m n p = refl

-- Exercise: Swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  -- This tripped me up; needed to use the left-version of
  -- this function over here; rather than swapping the arguments
  -- of cong, or something else.
  -- cong (+-comm m n) (_+ p)
  -- +-comm m n : n + m
  -- ≡⟨ cong ((+-comm m n) +_) p ⟩
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

-- Rewrite version; shorter, but means the explanations are comments,
-- which is annoying; far harder to see where you're going wrong.
+-swap' : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap' m n p
  rewrite sym (+-assoc m n p)      -- takes  m + (n + p) to (m + n) + p
        | cong (_+ p) (+-comm m n) -- takes (m + n) + p -> (n + m) + p
        | +-assoc n m p
  = refl


-- Multiplication is repeated addition:
--
--   4 * m = m + (m + (m + (m + zero)))
--
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero    n p = refl
*-distrib-+ (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + (m * p)) + (n * p)
  ≡⟨⟩
    p + (m * p) + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

-- From: https://github.com/kaaass/plfa-exercise/blob/master/src/plfa/Induction.agda#L172
*-distrib-+' : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+' zero    n p = refl
*-distrib-+' (suc m) n p
  rewrite *-distrib-+ m n p
        | sym (+-assoc p (m * p) (n * p))
  = refl

-- Glancing here: https://github.com/AlistairB/plfa/blob/master/src/part1/Induction.agda
*-identityʳ : ∀ (m : ℕ) → m * (suc zero) ≡ m
*-identityʳ zero =
  begin
    zero * suc zero
  ≡⟨⟩
    zero
  ∎
*-identityʳ (suc m) =
  begin
    (suc m) * (suc zero)
  ≡⟨⟩
    suc m * suc zero
  ≡⟨⟩
    suc (m * suc zero)
  ≡⟨ cong ((suc zero) +_) (*-identityʳ m) ⟩
    -- suc zero + (m * (suc zero)) ≡ suc zero + m
    suc m
  ∎

*-assoc' : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc' zero    n p = refl
*-assoc' (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ (*-distrib-+ n (m * n) p) ⟩
    (n * p) + ((m * n) * p)
  ≡⟨ cong ((n * p) +_) (*-assoc' m n p) ⟩
    (n * p) + (m * (n * p))
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero    n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
        | *-assoc m n p
  = refl

*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc m)
  rewrite *-zeroʳ m
  = refl


*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  begin
    suc m * suc n
  ≡⟨⟩
    suc n + (m * suc n)
  ≡⟨ cong (suc n +_) (*-suc m n) ⟩
    suc n + (m + m * n)
  ≡⟨⟩
    suc (n + (m + m * n))
  ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
    suc (n + m + m * n)
  ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
    suc (m + n + m * n)
  ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
    suc (m + (n + m * n))
  ≡⟨⟩
    suc m + suc m * n
  ∎


*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zeroʳ m = refl
*-comm m (suc n) =
  begin
    m * (suc n)
  ≡⟨ *-suc m n ⟩
    m + (m * n)
  ≡⟨ cong (m +_) (*-comm m n)⟩
    m + (n * m)
  ≡⟨⟩
    (suc n) * m
  ∎


monus : ∀ (n : ℕ) → zero ∸ n ≡ zero
monus zero                    = refl
monus (suc n) rewrite monus n = refl -- With induction


{-
∸-|-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n ∸ p)
∸-|-assoc zero n p    =
  begin
    (zero ∸ n) ∸ p
  ≡⟨ cong (_∸ p) (monus n) ⟩
    zero ∸ p
  ≡⟨ monus p ⟩
    zero
  ≡⟨ sym (monus (n ∸ p)) ⟩
    zero ∸ (n ∸ p)
  ∎
∸-|-assoc (suc m) n p =
  begin
    ?
  ∎
-}


{-
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite +- comm n p
  rewrite sym (+-assoc m p n)
  rewrite +-comm (m + p) n
  = refl
-}
