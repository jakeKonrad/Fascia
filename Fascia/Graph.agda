{-# OPTIONS --safe #-}
{-

This file contains an encoding of the model of directed
acyclic graphs in An Initial-Algebra Approach to Directed Acyclic Graphs
by Jeremy Gibbons. Cubical Agda is an interesting place to do this because
it allows the DAMG to be encoded as a HIT. The advantange of the HIT is that
the laws are 'baked in' to the data type and in §Further Work
Gibbons says that it would be interesting to apply accumulations (Gibbons, 1993)
to DAMG but "... all these other initial algebras have
been `free', that is, with no laws. It is not immediately obvious how to define
accumulations on types with laws, since for these there may be different ways
of representing the same object, and hence different ways of computing the
same catamorphism on that object." I intend to explore this.

Jeremy Gibbons (1993). Upwards and downwards accumulations on trees. In Bird
et al. (1993), pages 122-138. A revised version appears in the Proceedings of
the Massey Functional Programming Workshop, 1992.

-}
module Fascia.Graph where

open import Cubical.Foundations.Prelude renaming (empty to isOnei0Absurd)
open import Cubical.Data.Nat
open import Cubical.Categories.Category

open Category

module _ where
  private
    variable
      ℓ ℓ' : Level
      A : ℕ → ℕ → Type ℓ

  data 𝔾 (A : ℕ → ℕ → Type ℓ) : ℕ → ℕ → Type (ℓ-suc ℓ)
  
  infix 6 _⫿_
  infixr 5 _⨾_

  _edges : ∀ m → 𝔾 A m m 

  data 𝔾 A where
    empty : 𝔾 A 0 0
    edge : 𝔾 A 1 1
    vert : ∀ m n → A m n → 𝔾 A m n
    _⫿_ : ∀ {m n p q} → 𝔾 A m n → 𝔾 A p q → 𝔾 A (m + p) (n + q)
    _⨾_ : ∀ {m n p} → 𝔾 A m n → 𝔾 A n p → 𝔾 A m p
    swap : ∀ m n → 𝔾 A (m + n) (n + m)
    beside-λ : ∀ {m n}→ (x : 𝔾 A m n) → empty ⫿ x ≡ x
    beside-ρ : ∀ {m n} → (x : 𝔾 A m n) → (λ i → 𝔾 A (+-zero m i) (+-zero n i)) [ x ⫿ empty ≡ x ]
    beside-α : ∀ {m n p q r s}
             → (x : 𝔾 A m n)
             → (y : 𝔾 A p q)
             → (z : 𝔾 A r s)
             → PathP (λ i → 𝔾 A (+-assoc m p r i) (+-assoc n q s i))
                     (x ⫿ (y ⫿ z))
                     ((x ⫿ y) ⫿ z)
    before-λ : ∀ {m n}
             → (x : 𝔾 A m n)
             → m edges ⨾ x ≡ x
    before-ρ : ∀ {m n}
             → (x : 𝔾 A m n)
             → x ⨾ n edges ≡ x
    before-α : ∀ {m n p q} → (x : 𝔾 A m n) → (y : 𝔾 A n p) → (z : 𝔾 A p q) → (x ⨾ y) ⨾ z ≡ x ⨾ y ⨾ z
    abiding : ∀ {m n p q r s}
            → (w : 𝔾 A m n)
            → (x : 𝔾 A n p)
            → (y : 𝔾 A q r)
            → (z : 𝔾 A r s)
            → (w ⨾ x) ⫿ (y ⨾ z) ≡ (w ⫿ y) ⨾ (x ⫿ z)
    swap-λ : ∀ m
           → PathP (λ i → 𝔾 A (+-zero m i) m)
                   (swap m 0)
                   (m edges)
    -- This bothers me. The swap-plus law requires a transport in order to be
    -- well typed which means there are multiple ways to define it. I could
    -- have put the transport on the other side. It is also the only the
    -- only law that needs a transport. The crux of the problem is that
    -- (swap m n ⫿ p edges) : 𝔾 A ((m + n) + p) ((n + m) + p)
    -- and
    -- (n edges ⫿ swap m p) : 𝔾 A (n + (m + p)) (n + (p + m))
    -- so in order to compose ('before') them the parentheses need to be
    -- rearranged. I don't know if it's possible to get around this.
    swap-plus : ∀ m n p
              → PathP (λ i → 𝔾 A (+-assoc m n p i) (+-assoc n p m (~ i))) 
                      (swap m (n + p))
                      ((swap m n ⫿ p edges)
                      ⨾ transport (λ i → 𝔾 A (+-assoc n m p i) (n + (p + m))) (n edges ⫿ swap m p))
    swap-law : ∀ {m n p q}
             → (x : 𝔾 A n p)
             → (y : 𝔾 A m q)
             → swap m n ⨾ (x ⫿ y) ⨾ swap p q ≡ y ⫿ x
    trunc : ∀ m n → isSet (𝔾 A m n) 
                  
  zero edges = empty
  (suc m) edges = edge ⫿ (m edges)

  dislocation-law : (m n : ℕ)
                  → (x : 𝔾 A m 0)
                  → (y : 𝔾 A 0 n)
                  → PathP (λ i → 𝔾 A (+-zero m (~ i)) n)
                          (x ⨾ y)
                          (x ⫿ y)
  dislocation-law m n x y i =
    hcomp
      (λ j → λ
        { (i = i0) → x ⨾ y
        ; (i = i1) →
          hcomp
            (λ k →
               λ { (j = i0) → (x ⫿ empty) ⨾ (empty ⫿ y)
                 ; (j = i1) → before-ρ x k ⫿ before-λ y k
                 })
            (abiding x empty empty y (~ j))
        })
      (beside-ρ x (~ i) ⨾ beside-λ y (~ i))

  𝔾Cat : (A : ℕ → ℕ → Type ℓ) → Category ℓ-zero (ℓ-suc ℓ)
  𝔾Cat A .ob = ℕ
  𝔾Cat A .Hom[_,_] = 𝔾 A
  𝔾Cat A .id {x} = x edges
  𝔾Cat A ._⋆_ = _⨾_
  𝔾Cat A .⋆IdL = before-λ 
  𝔾Cat A .⋆IdR = before-ρ 
  𝔾Cat A .⋆Assoc = before-α 
  𝔾Cat A .isSetHom {x} {y} = trunc x y

