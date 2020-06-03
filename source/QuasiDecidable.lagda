Martin Escardo, May 2020.

The quasidecidable propositions, defined below, generalize the
semidecidable propositions.  A weakening of the axiom of countable
choice is equivalent to the equivalence of semidecidability with
quasidecidability.

The quasidecidable propositions form a dominance, and their totality
defines the initial σ-frame.  A σ-frame is a poset with countable
joins and finite meets such that binary meets distribute over
countable joins.

We first work with a hypothetical collection of quasidecidable
propositions, and then we construct it assuming propositional
resizing. Can we construct them without resizing and without
higher-inductive types other than propositional truncation?

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥ ; ⊤)

module QuasiDecidable
        (fe  : Fun-Ext)
        (pe₀ : propext 𝓤₀)
        (pt  : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import DecidableAndDetachable
open import Dominance
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-EquivalenceExamples
open import UF-Yoneda
open import UF-SIP-Examples
open import UF-Embeddings
open import UF-Powerset


\end{code}

We now move to quasidecidable propositions, but we first review
semidecidable ones.

A proposition is semidecidable if it is a countable join of decidable
propositions. See the paper
https://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf
by Martin Escardo and Cory Knapp.

NB. Semidecidable propositions are called Rosolini propositions in the above reference.

\begin{code}

is-semidecidable : 𝓤 ̇ → 𝓤 ̇
is-semidecidable X = ∃ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

\end{code}

Exercise. X is semidecidable iff it is a countable join of decidable
propositions:

\begin{code}

is-semidecidable' : 𝓤 ̇ → 𝓤 ⁺ ̇
is-semidecidable' {𝓤} X = ∃ A ꞉ (ℕ → 𝓤 ̇ ), ((n : ℕ) → decidable (A n)) × (X ≃ (∃ n ꞉ ℕ , A n))

\end{code}

The following shows that we need to truncate, because the Cantor type
(ℕ → 𝟚) is certainly not the type of semidecidable propositions:

\begin{code}
semidecidability-data : 𝓤 ̇ → 𝓤 ̇
semidecidability-data X = Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

totality-of-semidecidability-data : is-univalent 𝓤₀
                                  → (Σ X ꞉ 𝓤₀ ̇ , semidecidability-data X) ≃ (ℕ → 𝟚)
totality-of-semidecidability-data ua =

  (Σ X ꞉ 𝓤₀ ̇ , Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)) ≃⟨ i   ⟩
  (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)) ≃⟨ ii  ⟩
  (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , (∃ n ꞉ ℕ , α n ≡ ₁) ≃ X) ≃⟨ iii ⟩
  (ℕ → 𝟚) × 𝟙 {𝓤₀}                                     ≃⟨ iv  ⟩
  (ℕ → 𝟚)                                              ■
 where
  i   = Σ-flip
  ii  = Σ-cong (λ α → Σ-cong (λ X → ≃-Sym'' (univalence-gives-funext ua)))
  iii = Σ-cong (λ α → singleton-≃-𝟙 (univalence-via-singletons→ ua (∃ n ꞉ ℕ , α n ≡ ₁)))
  iv  = 𝟙-rneutral
\end{code}

The type of semidecidable propositions is not a σ-frame unless we have
enough countable choice - see the Escardo-Knapp reference above.

The set of quasidecidable propositions, if it exists, is the smallest
collection of propositions containing 𝟘 and 𝟙 and closed under
countable joins.

Exercise. It exists under propositional resizing assumptions (just
take the intersection of all subsets with 𝟘 and 𝟙 as members and
closed under countable joins). This exercise is solved below.

We now assume that there is a smallest collection of types, called
quasidecidable, satisfying the above closure property. The types in
this collection are automatically propositions. The minimality
condition of the collection amounts to an induction principle.

\begin{code}

module hypothetical-quasidecidability

        (is-quasidecidable : 𝓤₀ ̇ → 𝓤₀ ̇ )

        (being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P))

        (𝟘-is-quasidecidable : is-quasidecidable 𝟘)

        (𝟙-is-quasidecidable : is-quasidecidable 𝟙)

        (quasidecidable-closed-under-ω-joins : (P : ℕ → 𝓤₀ ̇ )
          → ((n : ℕ) → is-quasidecidable (P n))
          → is-quasidecidable (∃ n ꞉ ℕ , P n))

        (quasidecidable-induction : ∀ {𝓤} (F : 𝓤₀ ̇ → 𝓤 ̇ )
          → ((P : 𝓤₀ ̇ ) → is-prop (F P))
          → F 𝟘
          → F 𝟙
          → ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
          → (P : 𝓤₀ ̇ ) →  is-quasidecidable P → F P)
     where

\end{code}

As promised, the quasidecidable types are automatically propositions,
with a proof by induction:

\begin{code}

 quasidecidable-types-are-props : ∀ P → is-quasidecidable P → is-prop P
 quasidecidable-types-are-props = quasidecidable-induction
                                   is-prop
                                   (λ P → being-prop-is-prop fe)
                                   𝟘-is-prop  𝟙-is-prop (λ P φ → ∃-is-prop)

\end{code}

We collect the quasidecidable propositions in the type 𝓠:

\begin{code}

 𝓠 : 𝓤₁ ̇
 𝓠 = Σ P ꞉ 𝓤₀ ̇ , is-quasidecidable P

 _is-true : 𝓠 → 𝓤₀ ̇
 _is-true (P , i) = P

 being-true-is-quasidecidable : (𝕡 : 𝓠) → is-quasidecidable (𝕡 is-true)
 being-true-is-quasidecidable (P , i) = i

 being-true-is-prop : (𝕡 : 𝓠) → is-prop (𝕡 is-true)
 being-true-is-prop (P , i) = quasidecidable-types-are-props P i

 𝓠→Ω : 𝓠 → Ω 𝓤₀
 𝓠→Ω (P , i) = P , quasidecidable-types-are-props P i

 𝓠→Ω-is-embedding : is-embedding 𝓠→Ω
 𝓠→Ω-is-embedding = NatΣ-is-embedding is-quasidecidable is-prop ζ ζ-is-embedding
  where
   ζ : (P : 𝓤₀ ̇ ) → is-quasidecidable P → is-prop P
   ζ = quasidecidable-types-are-props
   ζ-is-embedding : (P : 𝓤₀ ̇ ) → is-embedding (ζ P)
   ζ-is-embedding P = maps-of-props-are-embeddings (ζ P) (being-quasidecidable-is-prop P) (being-prop-is-prop fe)

 𝓠-is-set : is-set 𝓠
 𝓠-is-set = subtypes-of-sets-are-sets 𝓠→Ω
             (embeddings-are-lc 𝓠→Ω 𝓠→Ω-is-embedding)
             (Ω-is-set fe pe₀)

 ⊥ : 𝓠
 ⊥ = 𝟘 , 𝟘-is-quasidecidable

 ⊤ : 𝓠
 ⊤ = 𝟙 , 𝟙-is-quasidecidable

 ⋁ : (ℕ → 𝓠) → 𝓠
 ⋁ 𝕡 = (∃ n ꞉ ℕ , 𝕡 n is-true) ,
        quasidecidable-closed-under-ω-joins
          (λ n → 𝕡 n is-true)
          (λ n → being-true-is-quasidecidable (𝕡 n))

\end{code}

We formulate and prove induction on 𝓠 in two different, equivalent
ways. The first one is often more convenient in practice, and the
second one is conceptually more natural.

\begin{code}

 𝓠-induction : (G : 𝓠 → 𝓤 ̇ )
             → ((𝕡 : 𝓠) → is-prop (G 𝕡))
             → G ⊥
             → G ⊤
             → ((𝕡 : ℕ → 𝓠) → ((n : ℕ) → G (𝕡 n)) → G (⋁ 𝕡))
             → (𝕡 : 𝓠) → G 𝕡
 𝓠-induction {𝓤} G G-is-prop-valued g₀ g₁ gω (P , i) = γ
  where
   F :  𝓤₀ ̇ → 𝓤 ̇
   F P = Σ j ꞉ is-quasidecidable P , G (P , j)
   F-is-prop-valued : ∀ P → is-prop (F P)
   F-is-prop-valued P = Σ-is-prop (being-quasidecidable-is-prop P) (λ j → G-is-prop-valued (P , j))
   F₀ : F 𝟘
   F₀ = 𝟘-is-quasidecidable , g₀
   F₁ : F 𝟙
   F₁ = 𝟙-is-quasidecidable , g₁
   Fω : (Q : ℕ → 𝓤₀ ̇) → ((n : ℕ) → F (Q n)) → F (∃ n ꞉ ℕ , Q n)
   Fω Q φ = quasidecidable-closed-under-ω-joins Q (λ n → pr₁ (φ n)) ,
            gω (λ n → (Q n , pr₁ (φ n))) (λ n → pr₂ (φ n))
   δ : Σ j ꞉ is-quasidecidable P , G (P , j)
   δ = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω P i
   j : is-quasidecidable P
   j = pr₁ δ
   g : G (P , j)
   g = pr₂ δ
   γ : G (P , i)
   r : j ≡ i
   r = being-quasidecidable-is-prop P j i
   γ = transport (λ - → G (P , -)) r g

 𝓠-induction' : (𝓖 : 𝓠 → Ω 𝓤)
              → ⊥ ∈ 𝓖
              → ⊤ ∈ 𝓖
              → ((𝕡 : ℕ → 𝓠) → ((n : ℕ) → 𝕡 n ∈ 𝓖) → ⋁ 𝕡 ∈ 𝓖)
              → (𝕡 : 𝓠) → 𝕡 ∈ 𝓖
 𝓠-induction' {𝓤} 𝓖 = 𝓠-induction (λ (P , i) → pr₁ (𝓖 (P , i))) (λ (P , i) → pr₂ (𝓖 (P , i)))

\end{code}

The quasidecidable propositions form a dominance, with a proof by
quasidecidable-induction. The main dominance condition generalizes
closure under binary products (that is, conjunctions, or meets):

\begin{code}

 quasidecidable-closed-under-× : propext 𝓤₀
   → (P : 𝓤₀ ̇ )
   → is-quasidecidable P
   → (Q : 𝓤₀ ̇ )
   → (P → is-quasidecidable Q)
   → is-quasidecidable (P × Q)
 quasidecidable-closed-under-× pe = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω
  where
   F : 𝓤₀ ̇ → 𝓤₁ ̇
   F P = (Q : 𝓤₀ ̇ ) → (P → is-quasidecidable Q) → is-quasidecidable (P × Q)
   F-is-prop-valued : (P : 𝓤₀ ̇ ) → is-prop (F P)
   F-is-prop-valued P = Π-is-prop fe (λ Q → Π-is-prop fe (λ _ → being-quasidecidable-is-prop (P × Q)))
   F₀ : F 𝟘
   F₀ Q φ = transport is-quasidecidable r 𝟘-is-quasidecidable
    where
     r : 𝟘 ≡ 𝟘 × Q
     r = pe 𝟘-is-prop (λ (z , q) → 𝟘-elim z) unique-from-𝟘 pr₁
   F₁ : F 𝟙
   F₁ Q φ = transport is-quasidecidable r (φ *)
    where
     i : is-prop Q
     i = quasidecidable-types-are-props Q (φ *)
     r : Q ≡ 𝟙 × Q
     r = pe i (×-is-prop 𝟙-is-prop i) (λ q → (* , q)) pr₂
   Fω :  (P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n)
   Fω P f Q φ = γ
    where
     φ' : (n : ℕ) → P n → is-quasidecidable Q
     φ' n p = φ ∣ n , p ∣
     a : (n : ℕ) → is-quasidecidable (P n × Q)
     a n = f n Q (φ' n)
     b : is-quasidecidable (∃ n ꞉ ℕ , P n × Q)
     b = quasidecidable-closed-under-ω-joins (λ n → P n × Q) a
     c : (∃ n ꞉ ℕ , P n × Q) → ((∃ n ꞉ ℕ , P n) × Q)
     c s = (t , q)
      where
       t : ∃ n ꞉ ℕ , P n
       t = ∥∥-rec ∃-is-prop (λ (n , (p , q)) → ∣ n , p ∣) s
       i : is-prop Q
       i = quasidecidable-types-are-props Q (φ t)
       q : Q
       q = ∥∥-rec i (λ (n , (p , q)) → q) s
     d : ((∃ n ꞉ ℕ , P n) × Q) → (∃ n ꞉ ℕ , P n × Q)
     d (t , q) = ∥∥-functor (λ (n , p) → n , (p , q)) t
     r : (∃ n ꞉ ℕ , P n × Q) ≡ ((∃ n ꞉ ℕ , P n) × Q)
     r = pe ∃-is-prop
           (×-prop-criterion ((λ _ → ∃-is-prop) ,
                              (λ e → quasidecidable-types-are-props Q (φ e))))
           c d
     γ : is-quasidecidable ((∃ n ꞉ ℕ , P n) × Q)
     γ = transport is-quasidecidable r b

\end{code}

This condition automatically implies closure under Σ, or joins indexed
by quasidecidable propositions:

\begin{code}

 quasidecidable-closed-under-Σ : propext 𝓤₀
   → (P : 𝓤₀ ̇ )
   → (Q : P → 𝓤₀ ̇ )
   → is-quasidecidable P
   → ((p : P) → is-quasidecidable (Q p))
   → is-quasidecidable (Σ Q)
 quasidecidable-closed-under-Σ pe = D3-and-D5'-give-D5 pe is-quasidecidable
                                      (quasidecidable-types-are-props)
                                      (λ P Q' i j → quasidecidable-closed-under-× pe P i Q' j)

\end{code}

Notice that Σ Q is equivalent to ∃ Q as quasidecidable types are
propositions.

The following summarizes the dominance conditions:

\begin{code}

 quasidecidability-is-dominance : propext 𝓤₀ → is-dominance is-quasidecidable
 quasidecidability-is-dominance pe = being-quasidecidable-is-prop ,
                                     quasidecidable-types-are-props ,
                                     𝟙-is-quasidecidable ,
                                     quasidecidable-closed-under-Σ pe
\end{code}

We now show that binary meets (cartesian products) of quasidecidable
properties distribute over countable joins (existential
quantifications over ℕ). One direction is trivial, and the other
follows by induction:

\begin{code}

 quasidecidable-σ-frame-trivial :
     (P : 𝓤₀ ̇ )
   → is-quasidecidable P
   → (Q : ℕ → 𝓤₀ ̇ )
   → ((n : ℕ) → is-quasidecidable (Q n))
   → P × ∃ Q → ∃ n ꞉ ℕ , P × Q n
 quasidecidable-σ-frame-trivial P i Q φ (p , e) = ∥∥-rec ∃-is-prop (λ (n , q) → ∣ n , p , q ∣) e


 quasidecidable-σ-frame-non-trivial :
    (P : 𝓤₀ ̇ )
  → is-quasidecidable P
  → (Q : ℕ → 𝓤₀ ̇ )
  → ((n : ℕ) → is-quasidecidable (Q n))
  → (∃ n ꞉ ℕ , P × Q n) → P × ∃ Q
 quasidecidable-σ-frame-non-trivial P i Q j = γ
  where
   F : 𝓤₀ ̇ → 𝓤₁ ̇
   F P = (Q : ℕ → 𝓤₀ ̇ )
       → ((n : ℕ) → is-quasidecidable (Q n))
       → is-prop P → (∃ n ꞉ ℕ , P × Q n) → P × ∃ Q
   F-is-prop-valued : ∀ P → is-prop (F P)
   F-is-prop-valued P = Π-is-prop fe (λ Q →
                        Π-is-prop fe (λ φ →
                        Π-is-prop fe (λ i →
                        Π-is-prop fe (λ a →
                        ×-is-prop i ∃-is-prop))))
   F₀ : F 𝟘
   F₀ Q φ i e = 𝟘-elim (∥∥-rec 𝟘-is-prop (λ (n , z , q) → z) e)
   F₁ : F 𝟙
   F₁ Q φ i e = * , (∥∥-rec ∃-is-prop (λ (n , o , q) → ∣ n , q ∣) e)
   Fω : (P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ P)
   Fω P f Q φ i e = ∥∥-rec ∃-is-prop (λ (n , ep , q) → ep) e ,
                    ∥∥-rec ∃-is-prop (λ (n , ep , q) → ∣ n , q ∣) e
   γ : (∃ n ꞉ ℕ , P × Q n) → P × ∃ Q
   γ = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω P i Q j (quasidecidable-types-are-props P i)

\end{code}

Putting the two directions together with the aid of propositional
extensionality, we get the σ-frame distributive law:

\begin{code}

 quasidecidable-σ-frame : propext 𝓤₀
   → (P : 𝓤₀ ̇ )
   → is-quasidecidable P
   → (Q : ℕ → 𝓤₀ ̇ )
   → ((n : ℕ) → is-quasidecidable (Q n))
   → P × ∃ Q ≡ (∃ n ꞉ ℕ , P × Q n)
 quasidecidable-σ-frame pe P i Q φ =
   pe (×-is-prop (quasidecidable-types-are-props P i)
                 (quasidecidable-types-are-props (∃ Q)
                    (quasidecidable-closed-under-ω-joins Q φ)))
      ∃-is-prop
      (quasidecidable-σ-frame-trivial P i Q φ)
      (quasidecidable-σ-frame-non-trivial P i Q φ)

\end{code}

We now give the quasidecidable propositions the structure of a
σ-frame. We have already defined ⊥, ⊤ and ⋁. So it remains to define ∧
and prove the σ-frame axioms.

\begin{code}

 _∧_ : 𝓠 → 𝓠 → 𝓠
 (P , i) ∧ (Q , j) = (P × Q) , quasidecidable-closed-under-× pe₀ P i Q (λ _ → j)

 ∧-is-idempotent : (𝕡 : 𝓠) → 𝕡 ∧ 𝕡 ≡ 𝕡
 ∧-is-idempotent (P , i) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i
   r : P × P ≡ P
   r = pe₀ (×-is-prop i' i') i' pr₁ (λ p → (p , p))
   γ : ((P × P) , _) ≡ (P , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ∧-is-commutative : (𝕡 𝕢 : 𝓠) → 𝕡 ∧ 𝕢 ≡ 𝕢 ∧ 𝕡
 ∧-is-commutative (P , i) (Q , j) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i
   j' : is-prop Q
   j' = quasidecidable-types-are-props Q j
   r : P × Q ≡ Q × P
   r = pe₀ (×-is-prop i' j')
           (×-is-prop j' i')
           (λ (p , q) → (q , p))
           (λ (q , p) → (p , q))
   γ : ((P × Q) , _) ≡ ((Q × P) , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ∧-is-associative : (𝕡 𝕢 𝕣 : 𝓠) → 𝕡 ∧ (𝕢 ∧ 𝕣) ≡ (𝕡 ∧ 𝕢) ∧ 𝕣
 ∧-is-associative (P , i) (Q , j) (R , k) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i
   j' : is-prop Q
   j' = quasidecidable-types-are-props Q j
   k' : is-prop R
   k' = quasidecidable-types-are-props R k
   r : P × (Q × R) ≡ (P × Q) × R
   r = pe₀ (×-is-prop i' (×-is-prop j' k'))
           (×-is-prop (×-is-prop i' j') k')
           (λ (p , (q , r)) → ((p , q) , r))
           (λ ((p , q) , r) → (p , (q , r)))
   γ : ((P × (Q × R)) , _) ≡ (((P × Q) × R) , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ⊥-is-minimum : (𝕡 : 𝓠) → ⊥ ∧ 𝕡 ≡ ⊥
 ⊥-is-minimum (P , i) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i
   r : 𝟘 × P ≡ 𝟘
   r = pe₀ (×-is-prop 𝟘-is-prop i')
           𝟘-is-prop
           pr₁
           unique-from-𝟘
   γ : ((𝟘 × P) , _) ≡ (𝟘 , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ⊤-is-maximum : (𝕡 : 𝓠) → 𝕡 ∧ ⊤ ≡ 𝕡
 ⊤-is-maximum (P , i) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i
   r : P × 𝟙 ≡ P
   r = pe₀ (×-is-prop i' 𝟙-is-prop)
           i'
           (λ (p , _) → p)
           (λ p → (p , *))
   γ : ((P × 𝟙) , _) ≡ (P , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 _≤_ : 𝓠 → 𝓠 → 𝓤₁ ̇
 𝕡 ≤ 𝕢 = 𝕡 ∧ 𝕢 ≡ 𝕡

 ≤-is-prop-valued : (𝕡 𝕢 : 𝓠) → is-prop (𝕡 ≤ 𝕢)
 ≤-is-prop-valued 𝕡 𝕢 = 𝓠-is-set {𝕡 ∧ 𝕢} {𝕡}

 ≤-characterization→ : {𝕡 𝕢 : 𝓠} → 𝕡 ≤ 𝕢 → (𝕡 is-true → 𝕢 is-true)
 ≤-characterization→ {P , i} {Q , j} l p = γ
  where
   r : P × Q ≡ P
   r = ap (_is-true) l
   g : P → P × Q
   g = idtofun P (P × Q) (r ⁻¹)
   γ : Q
   γ = pr₂ (g p)

 ≤-characterization← : {𝕡 𝕢 : 𝓠} → (𝕡 is-true → 𝕢 is-true) → 𝕡 ≤ 𝕢
 ≤-characterization← {P , i} {Q , j} f = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i
   j' : is-prop Q
   j' = quasidecidable-types-are-props Q j
   r : P × Q ≡ P
   r = pe₀ (×-is-prop i' j') i' pr₁ (λ p → (p , f p))
   γ : ((P × Q) , _) ≡ (P , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ≤-characterization : {𝕡 𝕢 : 𝓠} → (𝕡 ≤ 𝕢) ≃ (𝕡 is-true → 𝕢 is-true)
 ≤-characterization {𝕡} {𝕢} = logically-equivalent-props-are-equivalent
                              (≤-is-prop-valued 𝕡 𝕢)
                              (Π-is-prop fe (λ _ → being-true-is-prop 𝕢))
                              (≤-characterization→ {𝕡} {𝕢})
                              (≤-characterization← {𝕡} {𝕢})

\end{code}

NB. We can't conclude equality above because the lhs and rhs live in
different universes and hence in different types.

\begin{code}

 distributivity : (𝕡 : 𝓠) (𝕢 : ℕ → 𝓠) → 𝕡 ∧ (⋁ 𝕢) ≡ ⋁ (n ↦ 𝕡 ∧ 𝕢 n)
 distributivity (P , i) 𝕢 = γ
  where
   Q : ℕ → 𝓤₀ ̇
   Q n = 𝕢 n is-true
   j : (n : ℕ) → is-quasidecidable (Q n)
   j n = being-true-is-quasidecidable (𝕢 n)
   r : P × (∃ n ꞉ ℕ , Q n) ≡ (∃ n ꞉ ℕ , P × Q n)
   r = quasidecidable-σ-frame pe₀ P i Q j
   γ : ((P × (∃ n ꞉ ℕ , Q n)) , _) ≡ ((∃ n ꞉ ℕ , P × Q n) , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ⋁-is-ub : (𝕡 : ℕ → 𝓠) → (n : ℕ) → 𝕡 n ≤ ⋁ 𝕡
 ⋁-is-ub 𝕡 = a
  where
   a : (n : ℕ) → 𝕡 n ≤ ⋁ 𝕡
   a n = ≤-characterization← (λ p → ∣ n , p ∣)

 ⋁-is-lb-of-ubs : (𝕡 : ℕ → 𝓠) → (𝕦 : 𝓠) → ((n : ℕ) → 𝕡 n ≤ 𝕦) → ⋁ 𝕡 ≤ 𝕦
 ⋁-is-lb-of-ubs 𝕡 = b
  where
   b : (𝕦 : 𝓠) → ((n : ℕ) → 𝕡 n ≤ 𝕦) → ⋁ 𝕡 ≤ 𝕦
   b (U , i) φ = ≤-characterization← d
    where
     c : (Σ n ꞉ ℕ , 𝕡 n is-true) → U
     c (n , p) = ≤-characterization→ (φ n) p
     d : (∃ n ꞉ ℕ , 𝕡 n is-true) → U
     d = ∥∥-rec (quasidecidable-types-are-props U i) c

 open σ-frame

 QD : σ-Frame 𝓤₁
 QD = 𝓠 ,
     (⊤ , _∧_ , ⊥ , ⋁) ,
     (𝓠-is-set ,
      ∧-is-idempotent ,
      ∧-is-commutative ,
      ∧-is-associative ,
      ⊥-is-minimum ,
      ⊤-is-maximum ,
      distributivity ,
      ⋁-is-ub ,
      ⋁-is-lb-of-ubs)

\end{code}

Next we show that QD is the initial σ-frame. We first show that any
⊥,⊤,⋁-homomorphism on QD is automatically a ∧-homomorphism,
by 𝓠-induction.

\begin{code}

 ⊥⊤⋁-hom-on-QD-is-∧-hom : (𝓐 : σ-Frame 𝓤) (f : ⟨ QD ⟩ → ⟨ 𝓐 ⟩)
                        → f ⊥ ≡ ⊥⟨ 𝓐 ⟩
                        → f ⊤ ≡ ⊤⟨ 𝓐 ⟩
                        → ((λ 𝕡 → f (⋁ 𝕡)) ≡ (λ 𝕡 → ⋁⟨ 𝓐 ⟩ (n ↦ f (𝕡 n))))
                        → (λ 𝕡 𝕢 → f (𝕡 ∧ 𝕢)) ≡ (λ 𝕡 𝕢 → f 𝕡 ∧⟨ 𝓐 ⟩ f 𝕢)
 ⊥⊤⋁-hom-on-QD-is-∧-hom {𝓤} 𝓐 f f⊥ f⊤ f⋁ = γ
  where
   δ : (𝕡 𝕢 : 𝓠) → f (𝕡 ∧ 𝕢) ≡ (f 𝕡 ∧⟨ 𝓐 ⟩ f 𝕢)
   δ 𝕡 = 𝓠-induction (λ 𝕢 → f (𝕡 ∧ 𝕢) ≡ (f 𝕡 ∧⟨ 𝓐 ⟩ f 𝕢))
                     (λ 𝕢 → ⟨ 𝓐 ⟩-is-set {f (𝕡 ∧ 𝕢)} {f 𝕡 ∧⟨ 𝓐 ⟩ f 𝕢})
                     l₀ l₁ lω
    where
     l₀ = f (𝕡 ∧ ⊥)           ≡⟨ ap f (∧-is-commutative 𝕡 ⊥)     ⟩
          f (⊥ ∧ 𝕡)           ≡⟨ ap f (⊥-is-minimum 𝕡)           ⟩
          f ⊥                 ≡⟨ f⊥                              ⟩
          ⊥⟨ 𝓐 ⟩              ≡⟨ (⟨ 𝓐 ⟩-⊥-minimum (f 𝕡))⁻¹       ⟩
          (⊥⟨ 𝓐 ⟩ ∧⟨ 𝓐 ⟩ f 𝕡) ≡⟨ ap (λ - → - ∧⟨ 𝓐 ⟩ f 𝕡) (f⊥ ⁻¹) ⟩
          (f ⊥ ∧⟨ 𝓐 ⟩ f 𝕡)    ≡⟨ ⟨ 𝓐 ⟩-commutativity (f ⊥) (f 𝕡) ⟩
          (f 𝕡 ∧⟨ 𝓐 ⟩ f ⊥)    ∎

     l₁ = f (𝕡 ∧ ⊤)    ≡⟨ ap f (⊤-is-maximum 𝕡)    ⟩
          f 𝕡          ≡⟨ (⟨ 𝓐 ⟩-⊤-maximum (f 𝕡))⁻¹  ⟩
          (f 𝕡 ∧⟨ 𝓐 ⟩ ⊤⟨ 𝓐 ⟩)  ≡⟨ ap (λ - → f 𝕡 ∧⟨ 𝓐 ⟩ -) (f⊤ ⁻¹)     ⟩
          (f 𝕡 ∧⟨ 𝓐 ⟩ f ⊤) ∎

     lω : (𝕢 : ℕ → 𝓠)
        → ((n : ℕ) → f (𝕡 ∧ 𝕢 n) ≡ (f 𝕡 ∧⟨ 𝓐 ⟩ f (𝕢 n)))
        → f (𝕡 ∧ ⋁ 𝕢) ≡ (f 𝕡 ∧⟨ 𝓐 ⟩ f (⋁ 𝕢))
     lω 𝕢 φ = f (𝕡 ∧ ⋁ 𝕢)                         ≡⟨ ap f (distributivity 𝕡 𝕢)                          ⟩
              f ( ⋁ (n ↦ 𝕡 ∧ 𝕢 n))                ≡⟨ ap (λ - → - (n ↦ 𝕡 ∧ 𝕢 n)) f⋁                      ⟩
              ⋁⟨ 𝓐 ⟩ (n ↦ f (𝕡 ∧ 𝕢 n))            ≡⟨ ap ⋁⟨ 𝓐 ⟩ (dfunext fe φ)                           ⟩
              ⋁⟨ 𝓐 ⟩ (n ↦ f 𝕡 ∧⟨ 𝓐 ⟩ f (𝕢 n))     ≡⟨ (⟨ 𝓐 ⟩-distributivity (f 𝕡) (n ↦ f (𝕢 n)))⁻¹       ⟩
              (f 𝕡 ∧⟨ 𝓐 ⟩ ⋁⟨ 𝓐 ⟩ (n ↦ f (𝕢 n)))   ≡⟨ ap (λ - → meet 𝓐 (f 𝕡) -) (ap (λ - → - 𝕢) (f⋁ ⁻¹)) ⟩
              (f 𝕡 ∧⟨ 𝓐 ⟩ f (⋁ 𝕢))                ∎

   γ : (λ 𝕡 𝕢 → f (𝕡 ∧ 𝕢)) ≡ (λ 𝕡 𝕢 → f 𝕡 ∧⟨ 𝓐 ⟩ f 𝕢)
   γ = dfunext fe (λ 𝕡 → dfunext fe (δ 𝕡))

\end{code}

And then again by 𝓠-induction, there is at most one homomorphism from
𝓠 to any σ-frame:

\begin{code}

 at-most-one-hom : (𝓐 : σ-Frame 𝓤) (g h : 𝓠 → ⟨ 𝓐 ⟩)
                 → is-σ-frame-homomorphism QD 𝓐 g
                 → is-σ-frame-homomorphism QD 𝓐 h
                 → g ≡ h
 at-most-one-hom 𝓐 g h (g⊤ , g∧ , g⊥ , g⋁) (h⊤ , h∧ , h⊥ , h⋁) = dfunext fe r
  where
   i₀ = g ⊥    ≡⟨ g⊥ ⟩
        ⊥⟨ 𝓐 ⟩ ≡⟨ h⊥ ⁻¹ ⟩
        h ⊥    ∎

   i₁ = g ⊤    ≡⟨ g⊤    ⟩
        ⊤⟨ 𝓐 ⟩ ≡⟨ h⊤ ⁻¹ ⟩
        h ⊤    ∎

   iω : (𝕡 : ℕ → 𝓠) → ((n : ℕ) → g (𝕡 n) ≡ h (𝕡 n)) → g (⋁ 𝕡) ≡ h (⋁ 𝕡)
   iω 𝕡 φ = g (⋁ 𝕡)              ≡⟨ ap (λ - → - 𝕡) g⋁ ⟩
            ⋁⟨ 𝓐 ⟩ (n ↦ g (𝕡 n)) ≡⟨ ap ⋁⟨ 𝓐 ⟩ (dfunext fe φ)  ⟩
            ⋁⟨ 𝓐 ⟩ (n ↦ h (𝕡 n)) ≡⟨ (ap (λ - → - 𝕡) h⋁)⁻¹ ⟩
             h (⋁ 𝕡)             ∎

   r : g ∼ h
   r = 𝓠-induction (λ 𝕡 → g 𝕡 ≡ h 𝕡) (λ 𝕡 → ⟨ 𝓐 ⟩-is-set {g 𝕡} {h 𝕡}) i₀ i₁ iω

\end{code}

We now have enough constructions and lemmas to show that the type of
quasidecidable propositions is the initial σ-frame:

\begin{code}

 QD-is-initial-σ-Frame : (𝓐 : σ-Frame 𝓤)
                       → ∃! f ꞉ (⟨ QD ⟩ → ⟨ 𝓐 ⟩), is-σ-frame-homomorphism QD 𝓐 f
 QD-is-initial-σ-Frame {𝓤} 𝓐 = γ
  where

\end{code}

We first introduce some abbreviations for notational convenience:

\begin{code}

   A = ⟨ 𝓐 ⟩
   ⊥' = ⊥⟨ 𝓐 ⟩
   ⊤' = ⊤⟨ 𝓐 ⟩
   ⋁' = ⋁⟨ 𝓐 ⟩
   _≤'_ : A → A → 𝓤 ̇
   a ≤' b = a ≤⟨ 𝓐 ⟩ b
   _∧'_ : A → A → A
   a ∧' b = a ∧⟨ 𝓐 ⟩ b

\end{code}

We proceed by induction using the auxiliary predicate F.

The following condition in the definition of F says that the element a : A
is the least upper bound of the (weakly) constant family λ (p : P) → ⊤'.
Because least upper bounds are unique when they exist, the type F P is a
proposition.

\begin{code}

   F : 𝓤₀ ̇ → 𝓤 ̇
   F P = Σ a ꞉ A , (P → ⊤' ≤' a) × ((u : A) → (P → ⊤' ≤' u) → a ≤' u)

   F-is-prop-valued : (P : 𝓤₀ ̇ ) → is-prop (F P)
   F-is-prop-valued P (a , α , β) (a' , α' , β') = to-subtype-≡ j r
    where
     j : (a : A) → is-prop ((P → ⊤' ≤' a) × ((u : A) → (P → ⊤' ≤' u) → a ≤' u))
     j a = ×-is-prop
           (Π-is-prop fe (λ p → ⟨ 𝓐 ⟩-is-set {⊤' ∧' a} {⊤'}))
           (Π-is-prop fe (λ u →
            Π-is-prop fe (λ ψ → ⟨ 𝓐 ⟩-is-set {a ∧' u} {a})))
     r : a ≡ a'
     r = ⟨ 𝓐 ⟩-antisym a a' (β  a' α') (β' a α)

   F₀ : F 𝟘
   F₀ = ⊥' , (λ p → 𝟘-elim p) , (λ u ψ → ⟨ 𝓐 ⟩-⊥-minimum u)

   F₁ : F 𝟙
   F₁ = ⊤' , (λ p → ⟨ 𝓐 ⟩-⊤-maximum ⊤') , (λ u ψ → ψ *)

   Fω :  (P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n)
   Fω P φ = a∞ , α∞ , β∞
    where
     a : ℕ → A
     a n = pr₁ (φ n)
     α : (n : ℕ) → P n → ⊤' ≤' a n
     α n = pr₁ (pr₂ (φ n))
     β : (n : ℕ) → (u : A) → (P n → ⊤' ≤' u) → a n ≤' u
     β n = pr₂ (pr₂ (φ n))
     a∞ : A
     a∞ = ⋁' (n ↦ pr₁ (φ n))
     α∞ : (∃ n ꞉ ℕ , P n) → ⊤' ≤' a∞
     α∞ = ∥∥-rec ⟨ 𝓐 ⟩-is-set α∞'
      where
       α∞' : (Σ n ꞉ ℕ , P n) → ⊤' ≤' a∞
       α∞' (n , p) = ⟨ 𝓐 ⟩-trans ⊤' (a n) a∞ (α n p) (⟨ 𝓐 ⟩-⋁-is-ub a n)

     β∞ : (u : A) → ((∃ n ꞉ ℕ , P n) → ⊤' ≤' u) → a∞ ≤' u
     β∞ u ψ = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs a u l
      where
       l : (n : ℕ) → a n ≤' u
       l n = β n u (λ p → ψ ∣ n , p ∣)

   δ : (P : 𝓤₀ ̇) → is-quasidecidable P
     → Σ a ꞉ A , ((p : P) → ⊤' ≤' a) × ((u : A) → (P → ⊤' ≤' u) → a ≤' u)
   δ = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω

\end{code}

Using δ we define the desired homomorphism f:

\begin{code}

   f : 𝓠 → A
   f (P , i) = pr₁ (δ P i)

   αf : (𝕡 : 𝓠) → 𝕡 is-true → ⊤' ≤' f 𝕡
   αf (P , i) = pr₁ (pr₂ (δ P i))

   βf : (𝕡 : 𝓠) → ((u : A) → (𝕡 is-true → ⊤' ≤' u) → f 𝕡 ≤' u)
   βf (P , i) = pr₂ (pr₂ (δ P i))

\end{code}

The conditions αf and βf on f are crucial to prove that f is indeed a
homomorphism:

\begin{code}

   ⊤-preservation : f ⊤ ≡ ⊤'
   ⊤-preservation = ⟨ 𝓐 ⟩-antisym (f ⊤) ⊤' (⟨ 𝓐 ⟩-⊤-maximum (f ⊤)) (αf ⊤ *)

   ⊥-preservation : f ⊥ ≡ ⊥'
   ⊥-preservation = ⟨ 𝓐 ⟩-antisym (f ⊥) ⊥' (βf ⊥ ⊥' unique-from-𝟘) (⟨ 𝓐 ⟩-⊥-minimum (f ⊥))

   f-is-monotone : (𝕡 𝕢 : 𝓠) → 𝕡 ≤ 𝕢 → f 𝕡 ≤' f 𝕢
   f-is-monotone 𝕡 𝕢 l = βf 𝕡 (f 𝕢) (λ p → αf 𝕢 (≤-characterization→ l p))

   ⋁-preservation' : (𝕡 : ℕ → 𝓠) → f (⋁ 𝕡) ≡ ⋁' (n ↦ f (𝕡 n))
   ⋁-preservation' 𝕡 = ⟨ 𝓐 ⟩-antisym (f (⋁ 𝕡)) (⋁' (n ↦ f (𝕡 n))) v w
     where
      φ' : (Σ n ꞉ ℕ , 𝕡 n is-true) → ⊤' ≤' ⋁' (n ↦ f (𝕡 n))
      φ' (n , p) = ⟨ 𝓐 ⟩-trans ⊤' (f (𝕡 n)) (⋁' (n ↦ f (𝕡 n))) r s
        where
         r : ⊤' ≤' f (𝕡 n)
         r = αf (𝕡 n) p
         s : f (𝕡 n) ≤' ⋁' (n ↦ f (𝕡 n))
         s = ⟨ 𝓐 ⟩-⋁-is-ub (n ↦ f (𝕡 n)) n
      φ : (∃ n ꞉ ℕ , 𝕡 n is-true) → ⊤' ≤' ⋁' (n ↦ f (𝕡 n))
      φ = ∥∥-rec ⟨ 𝓐 ⟩-is-set φ'
      v : f (⋁ 𝕡) ≤' ⋁' (n ↦ f (𝕡 n))
      v = βf (⋁ 𝕡) (⋁' (n ↦ f (𝕡 n))) φ

      t' : (n : ℕ) → 𝕡 n ≤ ⋁ 𝕡
      t' = ⋁-is-ub 𝕡
      t : (n : ℕ) → f (𝕡 n) ≤' f (⋁ 𝕡)
      t n = f-is-monotone (𝕡 n) (⋁ 𝕡) (t' n)
      w : ⋁' (n ↦ f (𝕡 n)) ≤' f (⋁ 𝕡)
      w = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (n ↦ f (𝕡 n)) (f (⋁ 𝕡)) t

   ⋁-preservation : (λ 𝕡 → f (⋁ 𝕡)) ≡ (λ 𝕡 → ⋁' (n ↦ f (𝕡 n)))
   ⋁-preservation = dfunext fe ⋁-preservation'

\end{code}

By the above, binary meets are automatically preserved:

\begin{code}

   ∧-preservation : (λ 𝕡 𝕢 → f (𝕡 ∧ 𝕢)) ≡ (λ 𝕡 𝕢 → f 𝕡 ∧' f 𝕢)
   ∧-preservation = ⊥⊤⋁-hom-on-QD-is-∧-hom 𝓐 f ⊥-preservation ⊤-preservation ⋁-preservation

\end{code}

And then we are done:

\begin{code}

   f-is-hom : is-σ-frame-homomorphism QD 𝓐 f
   f-is-hom = ⊤-preservation , ∧-preservation , ⊥-preservation , ⋁-preservation

   γ : ∃! f ꞉ (⟨ QD ⟩ → ⟨ 𝓐 ⟩), is-σ-frame-homomorphism QD 𝓐 f
   γ = (f , f-is-hom) ,
       (λ (g , g-is-hom) → to-subtype-≡
                            (being-σ-frame-homomorphism-is-prop fe QD 𝓐)
                            (at-most-one-hom 𝓐 f g f-is-hom g-is-hom))
\end{code}

We discussed above the specification of the notion of quasidecidable
property. But can we define or construct it? Yes if, for example,
propositional resizing is available:

\begin{code}

open import UF-Size

module quasidecidability-construction-from-resizing
        (ρ : ∀ {𝓤} {𝓥} → propositional-resizing 𝓤 𝓥)
       where

\end{code}

This assunption says that any proposition in the universe 𝓤 is
equivalent to some proposition in the universe 𝓥, for any two
universes 𝓤 and 𝓥.

The crucial fact exploited here is that intersections of sets of
subsets 𝓐:𝓟(𝓟 X) exist under propositional resizing. We prove this
generalizing the type of 𝓐 (the double powerset) as follows, where the
membership relation defined in the module UF-Powerset has type

  _∈_ : {X : 𝓤 ̇ } → X → (X → Ω 𝓥) → 𝓥 ̇

\begin{code}

 intersections-exist : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦))
                     → Σ B ꞉ (X → Ω 𝓥) , ((x : X) → (x ∈ B) ⇔ ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A))
 intersections-exist {𝓤} {𝓥} {𝓦} {X} 𝓐 = B , (λ x → lr x , rl x)
  where
   β : X → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ̇
   β x = (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A

   i : (x : X) → is-prop (β x)
   i x = Π-is-prop fe (λ A → Π-is-prop fe (λ _ → ∈-is-prop A x))

   B : X → Ω 𝓥
   B x = (resize ρ (β x) (i x) , resize-is-prop ρ (β x) (i x))

   lr : (x : X) → x ∈ B → (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A
   lr x = from-resize ρ (β x) (i x)

   rl : (x : X) → ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A) → x ∈ B
   rl x = to-resize ρ (β x) (i x)

 ⋂ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) → (X → Ω 𝓥)
 ⋂ 𝓐 = pr₁ (intersections-exist 𝓐)

 from-⋂ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
        → x ∈ ⋂ 𝓐 → (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A
 from-⋂ 𝓐 x = lr-implication (pr₂ (intersections-exist 𝓐) x)

 to-⋂ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
      → ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A) → x ∈ ⋂ 𝓐
 to-⋂ 𝓐 x = rl-implication (pr₂ (intersections-exist 𝓐) x)

\end{code}

To define the type of quasi-decidable propositions, we take the
intersection of the types satisfying the following closure condition:

\begin{code}

 Ω₀ = Ω 𝓤₀

 QD-closed-types : (𝓤 ̇ → Ω₀) → Ω (𝓤 ⁺)
 QD-closed-types {𝓤} A = closure-condition , i
  where
   closure-condition : 𝓤 ⁺ ̇
   closure-condition = (𝟘 ∈ A)
                     × (𝟙 ∈ A)
                     × ((P : ℕ → 𝓤 ̇ ) → ((n : ℕ) → P n ∈ A) → (∃ n ꞉ ℕ , P n) ∈ A)
   i : is-prop closure-condition
   i = ×-is-prop (∈-is-prop A 𝟘)
      (×-is-prop (∈-is-prop A 𝟙)
                 (Π-is-prop fe (λ P →
                  Π-is-prop fe (λ _ → ∈-is-prop A (∃ n ꞉ ℕ , P n)))))

 is-quasidecidable : 𝓤₀ ̇ → 𝓤₀ ̇
 is-quasidecidable P = P ∈ ⋂ QD-closed-types

 being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P)
 being-quasidecidable-is-prop = ∈-is-prop (⋂ QD-closed-types)

 𝟘-is-quasidecidable : is-quasidecidable 𝟘
 𝟘-is-quasidecidable = to-⋂ QD-closed-types 𝟘 (λ A (c₀ , c₁ , cω) → c₀)

 𝟙-is-quasidecidable : is-quasidecidable 𝟙
 𝟙-is-quasidecidable = to-⋂ QD-closed-types 𝟙 (λ A (c₀ , c₁ , cω) → c₁)

 quasidecidable-closed-under-ω-joins : (P : ℕ → 𝓤₀ ̇ )
                                     → ((n : ℕ) → is-quasidecidable (P n))
                                     → is-quasidecidable (∃ n ꞉ ℕ , P n)
 quasidecidable-closed-under-ω-joins P φ = to-⋂ QD-closed-types (∃ P) γ
  where
   γ : (A : 𝓤₀ ̇ → Ω 𝓤₀) → A ∈ QD-closed-types → ∃ P ∈ A
   γ = from-⋂ QD-closed-types (∃ P) iv
    where
     i : (n : ℕ) → P n ∈ ⋂ QD-closed-types
     i = φ
     ii : (n : ℕ) (A : 𝓤₀ ̇ → Ω 𝓤₀) → A ∈ QD-closed-types → P n ∈ A
     ii n = from-⋂ QD-closed-types (P n) (i n)
     iii : (A : 𝓤₀ ̇ → Ω₀) → A ∈ QD-closed-types → ∃ P ∈ A
     iii A (c₁ , c₂ , cω) = cω P (λ n → ii n A (c₁ , c₂ , cω))
     iv : ∃ P ∈ ⋂ QD-closed-types
     iv = to-⋂ QD-closed-types (∃ P) iii

\end{code}

The full induction principle requires an application of resizing. We
first prove a particular case that doesn't, which captures the essence
of the proof of the full induction principle:

\begin{code}

 quasidecidable-induction₀ : (F : 𝓤₀ ̇ → 𝓤₀ ̇ )
   → ((P : 𝓤₀ ̇ ) → is-prop (F P))
   → F 𝟘
   → F 𝟙
   → ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
   → (P : 𝓤₀ ̇ ) →  is-quasidecidable P → F P
 quasidecidable-induction₀ F F-is-prop-valued F₀ F₁ Fω P P-is-quasidecidable = γ
  where
   A : (P : 𝓤₀ ̇ ) → Ω 𝓤₀
   A P = F P , F-is-prop-valued P
   A-is-QD-closed : A ∈ QD-closed-types
   A-is-QD-closed = F₀ , F₁ , Fω
   pqd : P ∈ ⋂ QD-closed-types
   pqd = P-is-quasidecidable
   δ : P ∈ A
   δ = from-⋂ QD-closed-types P pqd A A-is-QD-closed
   γ : F P
   γ = δ

\end{code}

To get the full induction principle we need to add resizing coercions
to the above construction. The point is that the type of F now
is 𝓤₀ ̇ → 𝓤 ̇ rather than 𝓤₀ ̇ → 𝓤₀ ̇ as above.

\begin{code}

 quasidecidable-induction : (F : 𝓤₀ ̇ → 𝓤 ̇ )
   → ((P : 𝓤₀ ̇ ) → is-prop (F P))
   → F 𝟘
   → F 𝟙
   → ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
   → (P : 𝓤₀ ̇ ) →  is-quasidecidable P → F P
 quasidecidable-induction {𝓤} F F-is-prop-valued F₀ F₁ Fω P i = γ
  where
   A : (P : 𝓤₀ ̇ ) → Ω 𝓤₀
   A P = resize ρ (F P) (F-is-prop-valued P) , resize-is-prop ρ (F P) (F-is-prop-valued P)
   A-is-QD-closed : A ∈ QD-closed-types
   A-is-QD-closed = to-resize ρ (F 𝟘) (F-is-prop-valued 𝟘) F₀ ,
                    to-resize ρ (F 𝟙) (F-is-prop-valued 𝟙) F₁ ,
                    (λ P φ  → to-resize ρ (F (∃ P)) (F-is-prop-valued (∃ P)) (Fω P (λ n → from-resize ρ (F (P n)) (F-is-prop-valued (P n)) (φ n))))
   pqd : P ∈ ⋂ QD-closed-types
   pqd = i
   δ : P ∈ A
   δ = from-⋂ QD-closed-types P i A A-is-QD-closed
   γ : F P
   γ = from-resize ρ (F P) (F-is-prop-valued P) δ

\end{code}

Hence the initial σ-frame exists under proposition resizing: we simply
plug the construction of the quasidecidable propositions to the above
hypothetical development.

\begin{code}

 open σ-frame

 initial-σ-Frame-exists :
  Σ I ꞉ σ-Frame 𝓤₁ , ((𝓐 : σ-Frame 𝓤) → ∃! f ꞉ (⟨ I ⟩ → ⟨ 𝓐 ⟩), is-σ-frame-homomorphism I 𝓐 f)
 initial-σ-Frame-exists {𝓤} = QD , QD-is-initial-σ-Frame
  where
   open hypothetical-quasidecidability
          is-quasidecidable
          being-quasidecidable-is-prop
          𝟘-is-quasidecidable
          𝟙-is-quasidecidable
          quasidecidable-closed-under-ω-joins
          quasidecidable-induction

\end{code}

The initial σ-frame can also be constructed as a higher-inductive type.

TODO. The initial ω-sup-lattice should be automatically the initial
σ-frame.

TODO. If the initial σ-frame exists, then we can define quasidecidable
propositions and show that they form a frame isomorphic (and hence
equal) to the initial σ-frame.

TODO. Write in Agda some of the proofs of the above reference with
Cory Knapp, particularly regarding choice. E.g. the semidecidable
properties form a dominance if and only if certain particular case of
countable choice holds.

TODO. This certain particular case of countable choice holds if and
only if the quasidecidable propositions are semidecidable. This is not
in the paper, but the methods of proof of the paper should apply more
or less directly.

TODO. Can we construct the collection of quasidecidable propositions
without resizing and without higher-inductive types other than
propositional truncation?
