module NaturalsEx where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

--
-- Following: https://plfa.github.io/Naturals/
--
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


one   = suc zero
two   = suc one
three = suc two
four  = suc three
five  = suc four
six   = suc five

seven : ℕ
seven = suc six

eight : ℕ
eight = 8

_+_ : ℕ → ℕ → ℕ
zero + n  = n
suc m + n = suc (m + n)
-- suc m + n   =
-- zero + n    = n
-- (suc m) + n = suc (m + n)


_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩ -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩ -- inductive
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩ -- base
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

_ : 3 + 3 ≡ 6
_ =
  begin
    3 + 3
  ≡⟨⟩
    suc (2 + 3)
  ≡⟨⟩
    6
  ∎


_ : 9 + 9 ≡ 18
_ = refl


_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
  ≡⟨⟩
    suc (suc (suc zero) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (zero + suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ∎


-- Now, multiplication!

-- Repeated addition
_*_ : ℕ → ℕ → ℕ
zero    * n = zero        -- 0       * n ≡ 0
(suc m) * n = n + (m * n) -- (1 + m) * n ≡ n + (m * n)


_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3) -- inductive: m = 1 (suc m = 2), n = 3
  ≡⟨⟩
    3 + (3 + (0 * 3)) -- m = 0, n = 3
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    -- m = 2 (suc m = 3), n = 4
    4 + (2 * 4)
  ≡⟨⟩
    --  m = 1, n = 4
    4 + (4 + (1 * 4))
  ≡⟨⟩
    -- m = 0, n = 4
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4))
  ≡⟨⟩
    12
  ∎

-- Monus: Like minus, but doesn't go smaller than zero.
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ : 3 ∸ 2 ≡ 1
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    -- m = 2, n = 1
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}


data Bin : Set where
  ⟨⟩  : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- 1011 = ⟨⟩ I 0 I I = ⟨⟩ 0 0 I 0 I I = 11 (decimal)

dec : Bin → Bin
dec ⟨⟩     = ⟨⟩
dec (⟨⟩ O) = ⟨⟩ O
dec (b I) = b O
dec (b O) = dec b I

_ : dec (⟨⟩ I I) ≡ ⟨⟩ I O
_ = refl

-- dec 0 = 0
_ : dec (⟨⟩ O) ≡ ⟨⟩ O
_ = refl

-- dec 1 = 0
_ : dec (⟨⟩ I) ≡ ⟨⟩ O
_ = refl

-- dec 2 = 1
_ : dec (⟨⟩ I O) ≡ ⟨⟩ O I
_ = refl

-- dec 3 = 2
_ : dec (⟨⟩ O I I) ≡ ⟨⟩ O I O
_ = refl

-- dec 4 = 3
_ : dec (⟨⟩ I O O) ≡ ⟨⟩ O I I
_ = refl
--
-- dec 5 = 4
_ : dec (⟨⟩ I O I) ≡ ⟨⟩ I O O
_ = refl

inc : Bin → Bin
inc ⟨⟩     = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ I I I I) ≡ ⟨⟩ I O O O O
_ = refl

-- inc 0 = 1
_ : inc (⟨⟩ O O O O) ≡ ⟨⟩ O O O I
_ = refl

-- inc 1 = 2
_ : inc (⟨⟩ O O O I) ≡ ⟨⟩ O O I O
_ = refl

-- inc 2 = 3
_ : inc (⟨⟩ O O I O) ≡ ⟨⟩ O O I I
_ = refl

-- inc 3 = 4
_ : inc (⟨⟩ O O I I) ≡ ⟨⟩ O I O O
_ = refl

-- inc 4 = 5
_ : inc (⟨⟩ O I O O) ≡ ⟨⟩ O I O I
_ = refl

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

_ : to 5 ≡ ⟨⟩ I O I
_ = refl

from : Bin → ℕ
from ⟨⟩     = 0
from (b O) =      2 * from b
from (b I) = 1 + (2 * from b)

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

_ : from (⟨⟩ I I I I I I I I) ≡ 255
_ = refl

_ : dec (to 500) ≡ to 499
_ = refl

-- Standard location for these things:
-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
