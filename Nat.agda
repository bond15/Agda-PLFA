
module Nat where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  z : ℕ
  s : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ -> ℕ -> ℕ
z + n = n
(s n) + m = s (n + m)

-- example evaulation
-- all of these steps are definitionally equal
-- and normalize to (s(s(s(s(s z)))))
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (s (s z)) + (s (s (s z)))
  ≡⟨⟩
    s (s z) + (s (s (s z)))
  ≡⟨⟩
    s ((s z) + (s (s (s z))))
  ≡⟨⟩
    s (s (z + (s (s (s z)))))
  ≡⟨⟩
    s (s (s (s (s z))))
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ -- 2 ≡ (s 1)
    (s 1) + 3
  ≡⟨⟩ -- apply RHS of inductive case
    (s (1 + 3))
  ≡⟨⟩ -- 1 ≡ (s 0)
    (s ((s 0) + 3))
  ≡⟨⟩ -- apply RHS of inductive case
    (s (s (0 + 3)))
  ≡⟨⟩ -- 0 + 3 ≡ 3 by base case
    (s (s 3))
  ≡⟨⟩
    5
  ∎

-- multiplication is repeated addition
_*_ : ℕ -> ℕ -> ℕ
0 * n = 0
(s m) * n = n + (m * n)

-- example
_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    (s 1) * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + ((s 0) * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    3 + 3
  ≡⟨⟩
    6
  ∎
-- exponentiation is repeated multiplication
_^_ : ℕ -> ℕ -> ℕ
m ^ 0 = 1
m ^ (s n) = m * (m ^ n)

-- monus (\.-)
_∸_ : ℕ -> ℕ -> ℕ
m ∸ 0 = m
0 ∸ m = 0 -- no negatives
(s m) ∸ (s n) = m ∸ n -- subtract one from each side

-- specify fixity (level and associativity (left biased))
infixl 6 _+_ _∸_
infixl 7 _*_

-- hole interaction
-- ?   indicate hole
-- C-c C-f  next hold
-- C-c C-c  case split
-- C-c C-,  goal and context
-- C-c C-<space>  fill hole
_foo_ : ℕ -> ℕ -> ℕ
z foo n = n
s m foo n = m


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin
