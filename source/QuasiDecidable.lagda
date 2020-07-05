Martin Escardo, 30 May - 3rd June 2020.

The quasidecidable propositions, defined below, generalize the
semidecidable propositions.  A weakening of the axiom of countable
choice is equivalent to the equivalence of semidecidability with
quasidecidability.

The quasidecidable propositions form a dominance, and their totality
defines the initial σ-frame.  A σ-frame is a poset with countable
joins and finite meets such that binary meets distribute over
countable joins.

  * We first work with a hypothetical collection of quasidecidable
    propositions and show that they form the initial σ-frame.

    This is in the submodule hypothetical-quasidecidability.


  * Then we construct it assuming propositional resizing.

    This is in the submodule quasidecidability-construction-from-resizing.


Can we construct them without resizing and without higher-inductive
types other than propositional truncation?

In this module, and hence the submodules, we assume function
extensionality, propositional extensionality and the existence of
propositional truncations, as explicit hypotheses.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥ ; ⊤)

module QuasiDecidable
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
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

Before considering quasidecidable propositions, we review
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

𝓢 : 𝓤₁ ̇
𝓢 = Σ X ꞉ 𝓤₀ ̇ , is-semidecidable X

\end{code}

The type 𝓢 of semidecidable propositions is not a σ-frame unless we
have enough countable choice - see the Escardo-Knapp reference above.

The set of quasidecidable propositions, if it exists, is the smallest
collection of propositions containing 𝟘 and 𝟙 and closed under
countable joins.

Exercise. It exists under propositional resizing assumptions (just
take the intersection of all subsets with 𝟘 and 𝟙 as members and
closed under countable joins). This exercise is solved below in the
submodule quasidecidability-construction-from-resizing.

We now assume that there is a such a smallest collection of types,
called quasidecidable, satisfying the above closure property. The
types in this collection are automatically propositions. The
minimality condition of the collection amounts to an induction
principle.

\begin{code}

module hypothetical-quasidecidability

        (is-quasidecidable : 𝓤₀ ̇ → 𝓤₀ ̇ )

        (being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P))

        (𝟘-is-quasidecidable : is-quasidecidable 𝟘)

        (𝟙-is-quasidecidable : is-quasidecidable 𝟙)

        (quasidecidable-closed-under-ω-joins :
            (P : ℕ → 𝓤₀ ̇ )
          → ((n : ℕ) → is-quasidecidable (P n))
          → is-quasidecidable (∃ n ꞉ ℕ , P n))

        (quasidecidable-induction : ∀ {𝓤}
            (F : 𝓤₀ ̇ → 𝓤 ̇ )
          → ((P : 𝓤₀ ̇ ) → is-prop (F P))
          → F 𝟘
          → F 𝟙
          → ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
          → (P : 𝓤₀ ̇ ) → is-quasidecidable P → F P)
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
   ζ-is-embedding P = maps-of-props-are-embeddings (ζ P)
                       (being-quasidecidable-is-prop P) (being-prop-is-prop fe)

 𝓠-is-set : is-set 𝓠
 𝓠-is-set = subtypes-of-sets-are-sets 𝓠→Ω
             (embeddings-are-lc 𝓠→Ω 𝓠→Ω-is-embedding)
             (Ω-is-set fe pe)

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
   F-is-prop-valued P = Σ-is-prop
                         (being-quasidecidable-is-prop P)
                         (λ j → G-is-prop-valued (P , j))

   F₀ : F 𝟘
   F₀ = 𝟘-is-quasidecidable , g₀

   F₁ : F 𝟙
   F₁ = 𝟙-is-quasidecidable , g₁

   Fω : (Q : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (Q n)) → F (∃ n ꞉ ℕ , Q n)
   Fω Q φ = quasidecidable-closed-under-ω-joins Q (λ n → pr₁ (φ n)) ,
            gω (λ n → (Q n , pr₁ (φ n))) (λ n → pr₂ (φ n))

   δ : Σ j ꞉ is-quasidecidable P , G (P , j)
   δ = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω P i

   j : is-quasidecidable P
   j = pr₁ δ

   g : G (P , j)
   g = pr₂ δ

   r : j ≡ i
   r = being-quasidecidable-is-prop P j i

   γ : G (P , i)
   γ = transport (λ - → G (P , -)) r g


 𝓠-induction' : (𝓖 : 𝓠 → Ω 𝓤)
              → ⊥ ∈ 𝓖
              → ⊤ ∈ 𝓖
              → ((𝕡 : ℕ → 𝓠) → ((n : ℕ) → 𝕡 n ∈ 𝓖) → ⋁ 𝕡 ∈ 𝓖)
              → (𝕡 : 𝓠) → 𝕡 ∈ 𝓖

 𝓠-induction' {𝓤} 𝓖 = 𝓠-induction
                        (λ (P , i) → pr₁ (𝓖 (P , i)))
                        (λ (P , i) → pr₂ (𝓖 (P , i)))
\end{code}

The quasidecidable propositions form a dominance, with a proof by
quasidecidable-induction. The main dominance condition generalizes
closure under binary products (that is, conjunctions, or meets):

\begin{code}

 quasidecidable-closed-under-× :
     (P : 𝓤₀ ̇ )
   → is-quasidecidable P
   → (Q : 𝓤₀ ̇ )
   → (P → is-quasidecidable Q)
   → is-quasidecidable (P × Q)

 quasidecidable-closed-under-× = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω
  where
   F : 𝓤₀ ̇ → 𝓤₁ ̇
   F P = (Q : 𝓤₀ ̇ ) → (P → is-quasidecidable Q) → is-quasidecidable (P × Q)

   F-is-prop-valued : (P : 𝓤₀ ̇ ) → is-prop (F P)
   F-is-prop-valued P = Π-is-prop fe (λ Q →
                        Π-is-prop fe (λ _ → being-quasidecidable-is-prop (P × Q)))

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

 quasidecidable-closed-under-Σ :
     (P : 𝓤₀ ̇ )
   → (Q : P → 𝓤₀ ̇ )
   → is-quasidecidable P
   → ((p : P) → is-quasidecidable (Q p))
   → is-quasidecidable (Σ Q)

 quasidecidable-closed-under-Σ = D3-and-D5'-give-D5 pe is-quasidecidable
                                  (quasidecidable-types-are-props)
                                  (λ P Q' i j → quasidecidable-closed-under-× P i Q' j)

\end{code}

Notice that Σ Q is equivalent to ∃ Q as quasidecidable types are
propositions, and propositions are closed under Σ:

\begin{code}

 NB : (P : 𝓤₀ ̇ )
    → (Q : P → 𝓤₀ ̇ )
    → is-quasidecidable P
    → ((p : P) → is-quasidecidable (Q p))
    → Σ Q ≃ ∃ Q

 NB P Q i j = logically-equivalent-props-are-equivalent
               k
               ∃-is-prop
               (λ (p , q) → ∣ p , q ∣)
               (∥∥-rec k id)
  where
   k : is-prop (Σ Q)
   k = quasidecidable-types-are-props (Σ Q) (quasidecidable-closed-under-Σ P Q i j)

\end{code}

The following summarizes the dominance conditions:

\begin{code}

 quasidecidability-is-dominance : is-dominance is-quasidecidable
 quasidecidability-is-dominance = being-quasidecidable-is-prop ,
                                  quasidecidable-types-are-props ,
                                  𝟙-is-quasidecidable ,
                                  quasidecidable-closed-under-Σ
\end{code}

We now give the quasidecidable propositions the structure of a
σ-frame. We have already defined ⊥, ⊤ and ⋁. So it remains to define ∧
and prove the σ-frame axioms.

\begin{code}

 _∧_ : 𝓠 → 𝓠 → 𝓠
 (P , i) ∧ (Q , j) = (P × Q) , quasidecidable-closed-under-× P i Q (λ _ → j)

 ∧-is-idempotent : (𝕡 : 𝓠) → 𝕡 ∧ 𝕡 ≡ 𝕡
 ∧-is-idempotent (P , i) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i

   r : P × P ≡ P
   r = pe (×-is-prop i' i') i' pr₁ (λ p → (p , p))

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
   r = pe (×-is-prop i' j')
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
   r = pe (×-is-prop i' (×-is-prop j' k'))
          (×-is-prop (×-is-prop i' j') k')
          (λ (p , (q , r)) → ((p , q) , r))
          (λ ((p , q) , r) → (p , (q , r)))

   γ : ((P × (Q × R)) , _) ≡ (((P × Q) × R) , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 _≤_ : 𝓠 → 𝓠 → 𝓤₁ ̇
 𝕡 ≤ 𝕢 = 𝕡 ∧ 𝕢 ≡ 𝕡

 ⊥-is-minimum : (𝕡 : 𝓠) → ⊥ ≤ 𝕡
 ⊥-is-minimum (P , i) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i

   r : 𝟘 × P ≡ 𝟘
   r = pe (×-is-prop 𝟘-is-prop i')
          𝟘-is-prop
          pr₁
          unique-from-𝟘

   γ : ((𝟘 × P) , _) ≡ (𝟘 , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ⊤-is-maximum : (𝕡 : 𝓠) → 𝕡 ≤ ⊤
 ⊤-is-maximum (P , i) = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i

   r : P × 𝟙 ≡ P
   r = pe (×-is-prop i' 𝟙-is-prop)
          i'
          (λ (p , _) → p)
          (λ p → (p , *))

   γ : ((P × 𝟙) , _) ≡ (P , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ≤-is-prop-valued : (𝕡 𝕢 : 𝓠) → is-prop (𝕡 ≤ 𝕢)
 ≤-is-prop-valued 𝕡 𝕢 = 𝓠-is-set {𝕡 ∧ 𝕢} {𝕡}

 from-≤ : {𝕡 𝕢 : 𝓠} → 𝕡 ≤ 𝕢 → (𝕡 is-true → 𝕢 is-true)
 from-≤ {P , i} {Q , j} l p = γ
  where
   r : P × Q ≡ P
   r = ap (_is-true) l

   g : P → P × Q
   g = idtofun P (P × Q) (r ⁻¹)

   γ : Q
   γ = pr₂ (g p)

 to-≤ : {𝕡 𝕢 : 𝓠} → (𝕡 is-true → 𝕢 is-true) → 𝕡 ≤ 𝕢
 to-≤ {P , i} {Q , j} f = γ
  where
   i' : is-prop P
   i' = quasidecidable-types-are-props P i

   j' : is-prop Q
   j' = quasidecidable-types-are-props Q j

   r : P × Q ≡ P
   r = pe (×-is-prop i' j') i' pr₁ (λ p → (p , f p))

   γ : ((P × Q) , _) ≡ (P , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ∧-⋁-distributivity : (𝕡 : 𝓠) (𝕢 : ℕ → 𝓠) → 𝕡 ∧ (⋁ 𝕢) ≡ ⋁ (n ↦ 𝕡 ∧ 𝕢 n)
 ∧-⋁-distributivity (P , i) 𝕢 = γ
  where
   Q : ℕ → 𝓤₀ ̇
   Q n = 𝕢 n is-true

   j : (n : ℕ) → is-quasidecidable (Q n)
   j n = being-true-is-quasidecidable (𝕢 n)

   r : P × (∃ n ꞉ ℕ , Q n) ≡ (∃ n ꞉ ℕ , P × Q n)
   r = prop-frame-distr pe
        P (quasidecidable-types-are-props P i)
        Q (λ n → quasidecidable-types-are-props (Q n) (j n))

   γ : ((P × (∃ n ꞉ ℕ , Q n)) , _) ≡ ((∃ n ꞉ ℕ , P × Q n) , _)
   γ = to-subtype-≡ being-quasidecidable-is-prop r

 ⋁-is-ub : (𝕡 : ℕ → 𝓠) → (n : ℕ) → 𝕡 n ≤ ⋁ 𝕡
 ⋁-is-ub 𝕡 n = to-≤ (λ p → ∣ n , p ∣)

 ⋁-is-lb-of-ubs : (𝕡 : ℕ → 𝓠) → (𝕦 : 𝓠) → ((n : ℕ) → 𝕡 n ≤ 𝕦) → ⋁ 𝕡 ≤ 𝕦
 ⋁-is-lb-of-ubs 𝕡 (U , i) φ = to-≤ γ
  where
   δ : (Σ n ꞉ ℕ , 𝕡 n is-true) → U
   δ (n , p) = from-≤ (φ n) p

   γ : (∃ n ꞉ ℕ , 𝕡 n is-true) → U
   γ = ∥∥-rec (quasidecidable-types-are-props U i) δ

\end{code}

Putting these axioms together we get the σ-frame of quasidecidable
propositions:

\begin{code}

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
      ∧-⋁-distributivity ,
      ⋁-is-ub ,
      ⋁-is-lb-of-ubs)

\end{code}

To prove that QD is the initial σ-frame, we work with an arbitrary
frame 𝓐 in an arbitrary universe 𝓤:

\begin{code}

 module _ {𝓤 : Universe} (𝓐 : σ-Frame 𝓤) where

\end{code}

We introduce some abbreviations, private to this anonymous module, for
notational convenience:

\begin{code}

  private

    A = ⟨ 𝓐 ⟩
    ⊥' = ⊥⟨ 𝓐 ⟩
    ⊤' = ⊤⟨ 𝓐 ⟩
    ⋁' = ⋁⟨ 𝓐 ⟩
    _≤'_ : A → A → 𝓤 ̇
    a ≤' b = a ≤⟨ 𝓐 ⟩ b
    _∧'_ : A → A → A
    a ∧' b = a ∧⟨ 𝓐 ⟩ b

\end{code}

We first show that any ⊥,⊤,⋁-homomorphism on QD is automatically a
∧-homomorphism, by 𝓠-induction.

\begin{code}

  ⊥⊤⋁-hom-on-QD-is-∧-hom : (f : 𝓠 → A)
                         → f ⊥ ≡ ⊥'
                         → f ⊤ ≡ ⊤'
                         → ((λ 𝕡 → f (⋁ 𝕡)) ≡ (λ 𝕡 → ⋁' (n ↦ f (𝕡 n))))
                         → (λ 𝕡 𝕢 → f (𝕡 ∧ 𝕢)) ≡ (λ 𝕡 𝕢 → f 𝕡 ∧' f 𝕢)

  ⊥⊤⋁-hom-on-QD-is-∧-hom f f⊥ f⊤ f⋁ = γ
   where
    δ : (𝕡 𝕢 : 𝓠) → f (𝕡 ∧ 𝕢) ≡ (f 𝕡 ∧' f 𝕢)
    δ 𝕡 = 𝓠-induction (λ 𝕢 → f (𝕡 ∧ 𝕢) ≡ (f 𝕡 ∧' f 𝕢))
                      (λ 𝕢 → ⟨ 𝓐 ⟩-is-set {f (𝕡 ∧ 𝕢)} {f 𝕡 ∧' f 𝕢})
                      l₀ l₁ lω
     where
      l₀ = f (𝕡 ∧ ⊥)    ≡⟨ ap f (∧-is-commutative 𝕡 ⊥)     ⟩
           f (⊥ ∧ 𝕡)    ≡⟨ ap f (⊥-is-minimum 𝕡)           ⟩
           f ⊥          ≡⟨ f⊥                              ⟩
           ⊥'           ≡⟨ (⟨ 𝓐 ⟩-⊥-minimum (f 𝕡))⁻¹       ⟩
           (⊥' ∧' f 𝕡)  ≡⟨ ap (λ - → - ∧' f 𝕡) (f⊥ ⁻¹)     ⟩
           (f ⊥ ∧' f 𝕡) ≡⟨ ⟨ 𝓐 ⟩-commutativity (f ⊥) (f 𝕡) ⟩
           (f 𝕡 ∧' f ⊥) ∎

      l₁ = f (𝕡 ∧ ⊤)    ≡⟨ ap f (⊤-is-maximum 𝕡)       ⟩
           f 𝕡          ≡⟨ (⟨ 𝓐 ⟩-⊤-maximum (f 𝕡))⁻¹   ⟩
           (f 𝕡 ∧' ⊤')  ≡⟨ ap (λ - → f 𝕡 ∧' -) (f⊤ ⁻¹) ⟩
           (f 𝕡 ∧' f ⊤) ∎

      lω : (𝕢 : ℕ → 𝓠)
         → ((n : ℕ) → f (𝕡 ∧ 𝕢 n) ≡ (f 𝕡 ∧' f (𝕢 n)))
         → f (𝕡 ∧ ⋁ 𝕢) ≡ (f 𝕡 ∧' f (⋁ 𝕢))

      lω 𝕢 φ = f (𝕡 ∧ ⋁ 𝕢)               ≡⟨ ap f (∧-⋁-distributivity 𝕡 𝕢)                      ⟩
               f ( ⋁ (n ↦ 𝕡 ∧ 𝕢 n))      ≡⟨ ap (λ - → - (n ↦ 𝕡 ∧ 𝕢 n)) f⋁                      ⟩
               ⋁' (n ↦ f (𝕡 ∧ 𝕢 n))      ≡⟨ ap ⋁' (dfunext fe φ)                               ⟩
               ⋁' (n ↦ f 𝕡 ∧' f (𝕢 n))   ≡⟨ (⟨ 𝓐 ⟩-distributivity (f 𝕡) (n ↦ f (𝕢 n)))⁻¹       ⟩
               (f 𝕡 ∧' ⋁' (n ↦ f (𝕢 n))) ≡⟨ ap (λ - → meet 𝓐 (f 𝕡) -) (ap (λ - → - 𝕢) (f⋁ ⁻¹)) ⟩
               (f 𝕡 ∧' f (⋁ 𝕢))          ∎

    γ : (λ 𝕡 𝕢 → f (𝕡 ∧ 𝕢)) ≡ (λ 𝕡 𝕢 → f 𝕡 ∧' f 𝕢)
    γ = dfunext fe (λ 𝕡 → dfunext fe (δ 𝕡))

\end{code}

And then again by 𝓠-induction, there is at most one homomorphism from
𝓠 to any σ-frame:

\begin{code}

  at-most-one-hom : (g h : 𝓠 → A)
                  → is-σ-frame-homomorphism QD 𝓐 g
                  → is-σ-frame-homomorphism QD 𝓐 h
                  → g ≡ h

  at-most-one-hom g h (g⊤ , _ , g⊥ , g⋁) (h⊤ , _ , h⊥ , h⋁) = dfunext fe r
   where
    i₀ = g ⊥ ≡⟨ g⊥    ⟩
         ⊥'  ≡⟨ h⊥ ⁻¹ ⟩
         h ⊥ ∎

    i₁ = g ⊤ ≡⟨ g⊤    ⟩
         ⊤'  ≡⟨ h⊤ ⁻¹ ⟩
         h ⊤ ∎

    iω : (𝕡 : ℕ → 𝓠) → ((n : ℕ) → g (𝕡 n) ≡ h (𝕡 n)) → g (⋁ 𝕡) ≡ h (⋁ 𝕡)
    iω 𝕡 φ = g (⋁ 𝕡)          ≡⟨ ap (λ - → - 𝕡) g⋁     ⟩
             ⋁' (n ↦ g (𝕡 n)) ≡⟨ ap ⋁' (dfunext fe φ)  ⟩
             ⋁' (n ↦ h (𝕡 n)) ≡⟨ (ap (λ - → - 𝕡) h⋁)⁻¹ ⟩
             h (⋁ 𝕡)          ∎

    r : g ∼ h
    r = 𝓠-induction (λ 𝕡 → g 𝕡 ≡ h 𝕡) (λ 𝕡 → ⟨ 𝓐 ⟩-is-set {g 𝕡} {h 𝕡}) i₀ i₁ iω

\end{code}

The condition in the conclusion of the following initiality lemma says
that the element a : A is the least upper bound of the (weakly)
constant family λ (p : P) → ⊤'.  Because least upper bounds are unique
when they exist, the type in the conclusion of the lemma is a
proposition. This is crucial because the induction principle can be
applied to prop-valued predicates only.

\begin{code}

  initiality-lemma : (P : 𝓤₀ ̇ )
                   → is-quasidecidable P
                   → Σ a ꞉ A , (P → ⊤' ≤' a) × ((u : A) → (P → ⊤' ≤' u) → a ≤' u)

  initiality-lemma = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω
   where
    F : 𝓤₀ ̇ → 𝓤 ̇
    F P = Σ a ꞉ A , (P → ⊤' ≤' a) × ((u : A) → (P → ⊤' ≤' u) → a ≤' u)

    F-is-prop-valued : (P : 𝓤₀ ̇ ) → is-prop (F P)
    F-is-prop-valued P (a , α , β) (a' , α' , β') = γ
     where
      j : (a : A) → is-prop ((P → ⊤' ≤' a) × ((u : A) → (P → ⊤' ≤' u) → a ≤' u))
      j a = ×-is-prop
            (Π-is-prop fe (λ p → ⟨ 𝓐 ⟩-is-set {⊤' ∧' a} {⊤'}))
            (Π-is-prop fe (λ u →
             Π-is-prop fe (λ ψ → ⟨ 𝓐 ⟩-is-set {a ∧' u} {a})))

      r : a ≡ a'
      r = ⟨ 𝓐 ⟩-antisym a a' (β  a' α') (β' a α)

      γ : (a , α , β) ≡ (a' , α' , β')
      γ = to-subtype-≡ j r

    F₀ : F 𝟘
    F₀ = ⊥' , unique-from-𝟘 , (λ u ψ → ⟨ 𝓐 ⟩-⊥-minimum u)

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
      a∞ = ⋁' a

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

\end{code}

We now have enough constructions and lemmas to show that the type of
quasidecidable propositions is the initial σ-frame. It remains to show
that the function 𝓠 → A induced by the initiality lemma is a σ-frame
homomorphism.

\begin{code}

  QD-is-initial-σ-Frame : ∃! f ꞉ (⟨ QD ⟩ → ⟨ 𝓐 ⟩), is-σ-frame-homomorphism QD 𝓐 f
  QD-is-initial-σ-Frame = γ
   where
    f : 𝓠 → A
    f (P , i) = pr₁ (initiality-lemma P i)

    α : (𝕡 : 𝓠) → 𝕡 is-true → ⊤' ≤' f 𝕡
    α (P , i) = pr₁ (pr₂ (initiality-lemma P i))

    β : (𝕡 : 𝓠) → ((u : A) → (𝕡 is-true → ⊤' ≤' u) → f 𝕡 ≤' u)
    β (P , i) = pr₂ (pr₂ (initiality-lemma P i))

\end{code}

The conditions α and β on f are crucial to prove that f is indeed a
homomorphism, and are all we need for that purpose.

\begin{code}

    ⊤-preservation : f ⊤ ≡ ⊤'
    ⊤-preservation = ⟨ 𝓐 ⟩-antisym (f ⊤) ⊤' (⟨ 𝓐 ⟩-⊤-maximum (f ⊤)) (α ⊤ *)

    ⊥-preservation : f ⊥ ≡ ⊥'
    ⊥-preservation = ⟨ 𝓐 ⟩-antisym (f ⊥) ⊥' (β ⊥ ⊥' unique-from-𝟘) (⟨ 𝓐 ⟩-⊥-minimum (f ⊥))

    f-is-monotone : (𝕡 𝕢 : 𝓠) → 𝕡 ≤ 𝕢 → f 𝕡 ≤' f 𝕢
    f-is-monotone 𝕡 𝕢 l = β 𝕡 (f 𝕢) (λ p → α 𝕢 (from-≤ l p))

    ⋁-preservation' : (𝕡 : ℕ → 𝓠) → f (⋁ 𝕡) ≡ ⋁' (n ↦ f (𝕡 n))
    ⋁-preservation' 𝕡 = ⟨ 𝓐 ⟩-antisym (f (⋁ 𝕡)) (⋁' (n ↦ f (𝕡 n))) v w
      where
       φ' : (Σ n ꞉ ℕ , 𝕡 n is-true) → ⊤' ≤' ⋁' (n ↦ f (𝕡 n))
       φ' (n , p) = ⟨ 𝓐 ⟩-trans ⊤' (f (𝕡 n)) (⋁' (n ↦ f (𝕡 n))) r s
         where
          r : ⊤' ≤' f (𝕡 n)
          r = α (𝕡 n) p

          s : f (𝕡 n) ≤' ⋁' (n ↦ f (𝕡 n))
          s = ⟨ 𝓐 ⟩-⋁-is-ub (n ↦ f (𝕡 n)) n

       φ : (∃ n ꞉ ℕ , 𝕡 n is-true) → ⊤' ≤' ⋁' (n ↦ f (𝕡 n))
       φ = ∥∥-rec ⟨ 𝓐 ⟩-is-set φ'

       v : f (⋁ 𝕡) ≤' ⋁' (n ↦ f (𝕡 n))
       v = β (⋁ 𝕡) (⋁' (n ↦ f (𝕡 n))) φ

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
    ∧-preservation = ⊥⊤⋁-hom-on-QD-is-∧-hom f ⊥-preservation ⊤-preservation ⋁-preservation

\end{code}

And then we are done:

\begin{code}

    f-is-hom : is-σ-frame-homomorphism QD 𝓐 f
    f-is-hom = ⊤-preservation , ∧-preservation , ⊥-preservation , ⋁-preservation

    γ : ∃! f ꞉ (⟨ QD ⟩ → A), is-σ-frame-homomorphism QD 𝓐 f
    γ = (f , f-is-hom) ,
        (λ (g , g-is-hom) → to-subtype-≡
                             (being-σ-frame-homomorphism-is-prop fe QD 𝓐)
                             (at-most-one-hom f g f-is-hom g-is-hom))
\end{code}

This concludes the anonymous module and the module
hypothetical-quasidecidability.

We discussed above the specification of the notion of quasidecidable
proposition. But can we define or construct it? Yes if, for example,
propositional resizing is available:

\begin{code}

open import UF-Size

module quasidecidability-construction-from-resizing
        (ρ : ∀ {𝓤} {𝓥} → propositional-resizing 𝓤 𝓥)
       where

\end{code}

This assumption says that any proposition in the universe 𝓤 is
equivalent to some proposition in the universe 𝓥, for any two
universes 𝓤 and 𝓥.

The crucial fact exploited here is that intersections of collections
of subcollections 𝓐:𝓟(𝓟 X) exist under propositional resizing. We
prove this generalizing the type of 𝓐 (the double powerset of X) as
follows, where the membership relation defined in the module
UF-Powerset has type

  _∈_ : {X : 𝓤 ̇ } → X → (X → Ω 𝓥) → 𝓥 ̇

\begin{code}

 intersections-exist : {X : 𝓤 ̇ } (𝓐 : (X → Ω 𝓥) → Ω 𝓦)
                     → Σ B ꞉ (X → Ω 𝓥) , ((x : X) → x ∈ B ⇔ ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A))
 intersections-exist {𝓤} {𝓥} {𝓦} {X} 𝓐 = B , (λ x → lr x , rl x)
  where
   β : X → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ̇
   β x = (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A

   i : (x : X) → is-prop (β x)
   i x = Π-is-prop fe (λ A → Π-is-prop fe (λ _ → ∈-is-prop A x))

   B : X → Ω 𝓥
   B x = resize ρ (β x) (i x) ,
         resize-is-prop ρ (β x) (i x)

   lr : (x : X) → x ∈ B → (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A
   lr x = from-resize ρ (β x) (i x)

   rl : (x : X) → ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A) → x ∈ B
   rl x = to-resize ρ (β x) (i x)

 ⋂ : {X : 𝓤 ̇ } → ((X → Ω 𝓥) → Ω 𝓦) → (X → Ω 𝓥)
 ⋂ 𝓐 = pr₁ (intersections-exist 𝓐)

 from-⋂ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
        → x ∈ ⋂ 𝓐 → (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A
 from-⋂ 𝓐 x = lr-implication (pr₂ (intersections-exist 𝓐) x)

 to-⋂ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
      → ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A) → x ∈ ⋂ 𝓐
 to-⋂ 𝓐 x = rl-implication (pr₂ (intersections-exist 𝓐) x)

\end{code}

To define the type of quasi-decidable propositions, we take the
intersection of the collections of types satisfying the following
closure condition:

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

The full induction principle requires a further application of
resizing. We first prove a particular case that doesn't, which
captures the essence of the proof of the full induction principle:

\begin{code}

 quasidecidable-induction₀ :
     (F : 𝓤₀ ̇ → 𝓤₀ ̇ )
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
to the above construction. The point is that now F has values in any
universe 𝓤 rather than the first universe 𝓤₀ as above.

\begin{code}

 quasidecidable-induction :
     (F : 𝓤₀ ̇ → 𝓤 ̇ )
   → ((P : 𝓤₀ ̇ ) → is-prop (F P))
   → F 𝟘
   → F 𝟙
   → ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
   → (P : 𝓤₀ ̇ ) → is-quasidecidable P → F P

 quasidecidable-induction {𝓤} F F-is-prop-valued F₀ F₁ Fω P P-is-quasidecidable = γ
  where
   A : (P : 𝓤₀ ̇ ) → Ω 𝓤₀
   A P = resize ρ (F P) (F-is-prop-valued P) ,
         resize-is-prop ρ (F P) (F-is-prop-valued P)

   A-is-QD-closed : A ∈ QD-closed-types
   A-is-QD-closed = to-resize ρ (F 𝟘) (F-is-prop-valued 𝟘) F₀ ,
                    to-resize ρ (F 𝟙) (F-is-prop-valued 𝟙) F₁ ,
                    (λ P φ  → to-resize ρ (F (∃ P)) (F-is-prop-valued (∃ P))
                               (Fω P (λ n → from-resize ρ (F (P n)) (F-is-prop-valued (P n)) (φ n))))

   pqd : P ∈ ⋂ QD-closed-types
   pqd = P-is-quasidecidable

   δ : P ∈ A
   δ = from-⋂ QD-closed-types P P-is-quasidecidable A A-is-QD-closed

   γ : F P
   γ = from-resize ρ (F P) (F-is-prop-valued P) δ

\end{code}

Hence the initial σ-frame exists under propositional resizing: we
simply plug the construction of the quasidecidable propositions to the
above hypothetical development.

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

The initial σ-frame can also be constructed as a higher-inductive
type, as is well known.

TODO. The initial ω-sup-lattice should be automatically the initial
σ-frame.

TODO. If the initial σ-frame exists, then we can define quasidecidable
propositions and show that they form a frame isomorphic (and hence
equal) to the initial σ-frame.

TODO. Write in Agda some of the proofs of the above reference with
Cory Knapp, particularly regarding choice. E.g. the semidecidable
properties form a dominance if and only if a certain particular case
of countable choice holds.

TODO. This certain particular case of countable choice holds if and
only if the quasidecidable propositions are semidecidable. This is not
in the paper, but the methods of proof of the paper should apply more
or less directly.

To think about. Can we construct the collection of quasidecidable
propositions without resizing and without higher-inductive types other
than propositional truncation?

The type of propositions is a frame. But here we need its restricted
structure of a σ-frame:

\begin{code}

module Ω-is-σ-frame {𝓤 : Universe} where

 open σ-frame

 𝓞 = Ω 𝓤

 ⊤Ω : 𝓞
 ⊤Ω = 𝟙 , 𝟙-is-prop

 _∧Ω_ : 𝓞 → 𝓞 → 𝓞
 (P , i) ∧Ω (Q , j) = (P × Q) , ×-is-prop i j

 ⊥Ω : 𝓞
 ⊥Ω = 𝟘 , 𝟘-is-prop

 ⋁Ω : (ℕ → 𝓞) → 𝓞
 ⋁Ω 𝕡 = (∃ n ꞉ ℕ , 𝕡 n holds) , ∃-is-prop

 ∧Ω-is-idempotent : (𝕡 : 𝓞) → 𝕡 ∧Ω 𝕡 ≡ 𝕡
 ∧Ω-is-idempotent (P , i) = γ
  where
   r : P × P ≡ P
   r = pe (×-is-prop i i) i pr₁ (λ p → (p , p))

   γ : ((P × P) , _) ≡ (P , _)
   γ = to-subtype-≡ (λ _ → being-prop-is-prop fe) r

 ∧Ω-is-commutative : (𝕡 𝕢 : 𝓞) → 𝕡 ∧Ω 𝕢 ≡ 𝕢 ∧Ω 𝕡
 ∧Ω-is-commutative (P , i) (Q , j) = γ
  where
   r : P × Q ≡ Q × P
   r = pe (×-is-prop i j)
          (×-is-prop j i)
          (λ (p , q) → (q , p))
          (λ (q , p) → (p , q))

   γ : ((P × Q) , _) ≡ ((Q × P) , _)
   γ = to-subtype-≡ (λ _ → being-prop-is-prop fe) r

 ∧Ω-is-associative : (𝕡 𝕢 𝕣 : 𝓞) → 𝕡 ∧Ω (𝕢 ∧Ω 𝕣) ≡ (𝕡 ∧Ω 𝕢) ∧Ω 𝕣
 ∧Ω-is-associative (P , i) (Q , j) (R , k) = γ
  where
   r : P × (Q × R) ≡ (P × Q) × R
   r = pe (×-is-prop i (×-is-prop j k))
          (×-is-prop (×-is-prop i j) k)
          (λ (p , (q , r)) → ((p , q) , r))
          (λ ((p , q) , r) → (p , (q , r)))

   γ : ((P × (Q × R)) , _) ≡ (((P × Q) × R) , _)
   γ = to-subtype-≡ (λ _ → being-prop-is-prop fe) r -- is-prop r

 _≤Ω_ : 𝓞 → 𝓞 → 𝓤 ⁺ ̇
 𝕡 ≤Ω 𝕢 = 𝕡 ∧Ω 𝕢 ≡ 𝕡

 ⊥Ω-is-minimum : (𝕡 : 𝓞) → ⊥Ω ≤Ω 𝕡
 ⊥Ω-is-minimum (P , i) = γ
  where
   r : 𝟘 × P ≡ 𝟘
   r = pe (×-is-prop 𝟘-is-prop i)
          𝟘-is-prop
          pr₁
          unique-from-𝟘

   γ : ((𝟘 × P) , _) ≡ (𝟘 , _)
   γ = to-subtype-≡ (λ _ → being-prop-is-prop fe) r -- is-prop r

 ⊤Ω-is-maximum : (𝕡 : 𝓞) → 𝕡 ≤Ω ⊤Ω
 ⊤Ω-is-maximum (P , i) = γ
  where
   r : P × 𝟙 ≡ P
   r = pe (×-is-prop i 𝟙-is-prop)
          i
          (λ (p , _) → p)
          (λ p → (p , *))

   γ : ((P × 𝟙) , _) ≡ (P , _)
   γ = to-subtype-≡ (λ _ → being-prop-is-prop fe) r -- is-prop r

 ≤Ω-is-prop-valued : (𝕡 𝕢 : 𝓞) → is-prop (𝕡 ≤Ω 𝕢)
 ≤Ω-is-prop-valued 𝕡 𝕢 = Ω-is-set fe pe {𝕡 ∧Ω 𝕢} {𝕡}

 from-≤Ω : {𝕡 𝕢 : 𝓞} → 𝕡 ≤Ω 𝕢 → (𝕡 holds → 𝕢 holds)
 from-≤Ω {P , i} {Q , j} l p = γ
  where
   r : P × Q ≡ P
   r = ap (_holds) l

   g : P → P × Q
   g = idtofun P (P × Q) (r ⁻¹)

   γ : Q
   γ = pr₂ (g p)

 to-≤Ω : {𝕡 𝕢 : 𝓞} → (𝕡 holds → 𝕢 holds) → 𝕡 ≤Ω 𝕢
 to-≤Ω {P , i} {Q , j} f = γ
  where
   r : P × Q ≡ P
   r = pe (×-is-prop i j) i pr₁ (λ p → (p , f p))

   γ : ((P × Q) , _) ≡ (P , _)
   γ = to-subtype-≡ (λ _ → being-prop-is-prop fe) r -- is-prop r

 ∧-⋁-Ω-distributivity : (𝕡 : 𝓞) (𝕢 : ℕ → 𝓞) → 𝕡 ∧Ω (⋁Ω 𝕢) ≡ ⋁Ω (n ↦ 𝕡 ∧Ω 𝕢 n)
 ∧-⋁-Ω-distributivity (P , i) 𝕢 = γ
  where
   Q : ℕ → 𝓤 ̇
   Q n = 𝕢 n holds

   r : P × (∃ n ꞉ ℕ , Q n) ≡ (∃ n ꞉ ℕ , P × Q n)
   r = prop-frame-distr pe P i Q λ n → holds-is-prop (𝕢 n)

   γ : ((P × (∃ n ꞉ ℕ , Q n)) , _) ≡ ((∃ n ꞉ ℕ , P × Q n) , _)
   γ = to-subtype-≡ (λ _ → being-prop-is-prop fe) r

 ⋁Ω-is-ub : (𝕡 : ℕ → 𝓞) → (n : ℕ) → 𝕡 n ≤Ω ⋁Ω 𝕡
 ⋁Ω-is-ub 𝕡 n = to-≤Ω {𝕡 n} {⋁Ω 𝕡} (λ p → ∣ n , p ∣)

 ⋁Ω-is-lb-of-ubs : (𝕡 : ℕ → 𝓞) → (𝕦 : 𝓞) → ((n : ℕ) → 𝕡 n ≤Ω 𝕦) → ⋁Ω 𝕡 ≤Ω 𝕦
 ⋁Ω-is-lb-of-ubs 𝕡 (U , i) φ = to-≤Ω {⋁Ω 𝕡} {𝕦} γ
  where
   𝕦 = (U , i)

   δ : (Σ n ꞉ ℕ , 𝕡 n holds) → U
   δ (n , p) = from-≤Ω {𝕡 n} {𝕦} (φ n) p

   γ : (∃ n ꞉ ℕ , 𝕡 n holds) → U
   γ = ∥∥-rec i δ

 σΩ : σ-Frame (𝓤 ⁺)
 σΩ = 𝓞 ,
     (⊤Ω , _∧Ω_ , ⊥Ω , ⋁Ω) ,
     Ω-is-set fe pe ,
     ∧Ω-is-idempotent ,
     ∧Ω-is-commutative ,
     ∧Ω-is-associative ,
     ⊥Ω-is-minimum ,
     ⊤Ω-is-maximum ,
     ∧-⋁-Ω-distributivity ,
     ⋁Ω-is-ub ,
     ⋁Ω-is-lb-of-ubs

\end{code}

We now explore the consequences of the hypothetical existence of an
initial σ-frame.

\begin{code}

module hypothetical-initial-σ-Frame where

 open σ-frame

 module _ (𝓐 : σ-Frame 𝓤₀)
          (𝓐-is-initial : {𝓦 : Universe} (𝓑 : σ-Frame 𝓦)
                        → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩), is-σ-frame-homomorphism· 𝓐 𝓑 f)
        where

  private
   A   = ⟨ 𝓐 ⟩
   ⊥   = ⊥⟨ 𝓐 ⟩
   ⊤   = ⊤⟨ 𝓐 ⟩
   _∧_ = λ a b → a ∧⟨ 𝓐 ⟩ b
   ⋁  = ⋁⟨ 𝓐 ⟩

  σ-induction : (P : A → 𝓥 ̇ )
              → ((a : A) → is-prop (P a))
              → P ⊤
              → ((a b : A) → P a → P b → P (a ∧ b))
              → P ⊥
              → ((a : (ℕ → A)) → ((n : ℕ) → P (a n)) → P (⋁ a))
              → (a : A) → P a
  σ-induction {𝓥} P P-is-prop-valued ⊤-closure ∧-closure ⊥-closure ⋁-closure = γ
   where
    X = Σ a ꞉ A , P a

    ⊤' ⊥' : X
    ⊤' = (⊤ , ⊤-closure)
    ⊥' = (⊥ , ⊥-closure)

    _∧'_ : X → X → X
    (a , p) ∧' (b , q) = (a ∧ b , ∧-closure a b p q)

    ⋁' : (ℕ → X) → X
    ⋁' x = (⋁ (pr₁ ∘ x) , ⋁-closure (pr₁ ∘ x) (pr₂ ∘ x))

    X-is-set : is-set X
    X-is-set = subtypes-of-sets-are-sets pr₁
                (pr₁-lc (λ {a : A} → P-is-prop-valued a)) ⟨ 𝓐 ⟩-is-set

    ∧'-is-idempotent : (x : X) → x ∧' x ≡ x
    ∧'-is-idempotent (a , p) = to-subtype-≡ P-is-prop-valued (⟨ 𝓐 ⟩-idempotency a)

    ∧'-is-commutative : (x y : X) → x ∧' y ≡ y ∧' x
    ∧'-is-commutative (a , _) (b , _) = to-subtype-≡ P-is-prop-valued
                                         (⟨ 𝓐 ⟩-commutativity a b)

    ∧'-is-associative : (x y z : X) → x ∧' (y ∧' z) ≡ (x ∧' y) ∧' z
    ∧'-is-associative (a , _) (b , _) (c , _) = to-subtype-≡ P-is-prop-valued
                                                 (⟨ 𝓐 ⟩-associativity a b c)

    _≤'_ : X → X → 𝓥 ̇
    x ≤' y = x ∧' y ≡ x

    ⊤'-is-maximum : (x : X) → x ≤' ⊤'
    ⊤'-is-maximum (a , _) = to-subtype-≡ P-is-prop-valued
                             (⟨ 𝓐 ⟩-⊤-maximum a)

    ⊥'-is-minimum : (x : X) → ⊥' ≤' x
    ⊥'-is-minimum (a , _) = to-subtype-≡ P-is-prop-valued
                             (⟨ 𝓐 ⟩-⊥-minimum a)

    ∧'-⋁'-distributivity : (x : X) (y : ℕ → X) → x ∧' (⋁' y) ≡ ⋁' (n ↦ x ∧' y n)
    ∧'-⋁'-distributivity (x , _) y = to-subtype-≡ P-is-prop-valued
                                       (⟨ 𝓐 ⟩-distributivity x (pr₁ ∘ y))

    ⋁'-is-ub : (x : ℕ → X) → (n : ℕ) → x n ≤' ⋁' x
    ⋁'-is-ub x n = to-subtype-≡ P-is-prop-valued
                     (⟨ 𝓐 ⟩-⋁-is-ub (pr₁ ∘ x) n)

    ⋁'-is-lb-of-ubs : (x : ℕ → X) → (u : X) → ((n : ℕ) → x n ≤' u) → ⋁' x ≤' u
    ⋁'-is-lb-of-ubs x (a , _) φ = to-subtype-≡ P-is-prop-valued
                                    (⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (pr₁ ∘ x) a (λ n → ap pr₁ (φ n)))

    𝓑 : σ-Frame 𝓥
    𝓑 = X , (⊤' , _∧'_ , ⊥' , ⋁') ,
         X-is-set ,
         ∧'-is-idempotent ,
         ∧'-is-commutative ,
         ∧'-is-associative ,
         ⊥'-is-minimum ,
         ⊤'-is-maximum ,
         ∧'-⋁'-distributivity ,
         ⋁'-is-ub ,
         ⋁'-is-lb-of-ubs

    g : X → A
    g = pr₁

    g-is-homomorphism : is-σ-frame-homomorphism· 𝓑 𝓐 g
    g-is-homomorphism = refl , (λ a b → refl) , refl , (λ 𝕒 → refl)


    f : A → X
    f = pr₁ (center (𝓐-is-initial 𝓑))

    f-is-homomorphism : is-σ-frame-homomorphism· 𝓐 𝓑 f
    f-is-homomorphism = pr₂ (center (𝓐-is-initial 𝓑))

    h : A → A
    h = g ∘ f

    h-is-homomorphism : is-σ-frame-homomorphism· 𝓐 𝓐 h
    h-is-homomorphism = ∘-σ-frame-homomorphism· 𝓐 𝓑 𝓐 f g f-is-homomorphism g-is-homomorphism

    H : h ≡ id
    H = ap pr₁ p
     where
      p : (h , h-is-homomorphism) ≡ (id , id-is-σ-frame-homomorphism· 𝓐)
      p = singletons-are-props (𝓐-is-initial 𝓐) _ _

    δ : (a : A) → P (h a)
    δ a = pr₂ (f a)

    γ : (a : A) → P a
    γ a = transport P (happly H a) (δ a)


 {-
  f : A → 𝓞
  f = pr₁ (center (𝓐-initial σΩ))

  h : is-σ-frame-homomorphism 𝓐 σΩ f
  h = pr₂ (center (𝓐-initial σΩ))

  is-quasidecidable : 𝓤 ̇ → 𝓤 ⁺ ̇
  is-quasidecidable P = Σ i ꞉ is-prop P , ∃! 𝕡 ꞉ A , f 𝕡 ≡ (P , i)

  being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P)
  being-quasidecidable-is-prop P = Σ-is-prop (being-prop-is-prop fe) (λ i → ∃!-is-prop fe)

  𝟘-is-quasidecidable : is-quasidecidable 𝟘
  𝟘-is-quasidecidable = 𝟘-is-prop , (⊥A , pr₁ (pr₂ (pr₂ h))) , c
   where
    d : ((𝕡 , r) : Σ 𝕡 ꞉ A , f 𝕡 ≡ ⊥) → (⊥⟨ 𝓐 ⟩ , pr₁ (pr₂ (pr₂ h))) ≡ (𝕡 , r)
    d (𝕡 , r) = to-subtype-≡ (λ 𝕡 → ⟨ σΩ ⟩-is-set) question
     where
      r' : f 𝕡 ≡ ⊥
      r' = r
      question : ⊥⟨ 𝓐 ⟩ ≡ 𝕡
      question = {!!}
    c : ((𝕡 , r) : Σ 𝕡 ꞉ ⟨ 𝓐 ⟩ , f 𝕡 ≡ (𝟘 , 𝟘-is-prop)) → (⊥⟨ 𝓐 ⟩ , pr₁ (pr₂ (pr₂ h))) ≡ (𝕡 , r)
    c = d

  𝟙-is-quasidecidable : is-quasidecidable 𝟙
  𝟙-is-quasidecidable = {!!}

  quasidecidable-closed-under-ω-joins : (P : ℕ → 𝓤 ̇ )
                                      → ((n : ℕ) → is-quasidecidable (P n))
                                      → is-quasidecidable (∃ n ꞉ ℕ , P n)
  quasidecidable-closed-under-ω-joins P φ = ∃-is-prop , {!!}
   where
    φ' : (n : ℕ) → Σ i ꞉ is-prop (P n) , ∃ 𝕡 ꞉ A , f 𝕡 ≡ (P n , i)
    φ' = {!!}
    γ : Σ j ꞉ is-prop (∃ P) , ∃ 𝕢 ꞉ A , f 𝕢 ≡ (∃ P , j)
    γ = ∃-is-prop , ∥∥-rec ∃-is-prop {!!} {!!}

  quasidecidable-induction :
      (F : {!!} ̇ → 𝓤 ̇ )
    → ((P : {!!} ̇ ) → is-prop (F P))
    → F 𝟘
    → F 𝟙
    → ((P : ℕ → {!!} ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
    → (P : {!!} ̇ ) →  is-quasidecidable P → F P

  quasidecidable-induction = {!!}
 -}
\end{code}

We now explore the consequences of the hypothetical existence of an
initial σ-frame.

\begin{code}

module hypothetical-initial-σ-Sup-Lattice
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

 open import sigma-sup-lattice fe pe

 module _
        (𝓐 : σ-Sup-Lattice 𝓤₀ 𝓤₀)
        (𝓐-is-initial : {𝓤 𝓥 : Universe} (𝓑 : σ-Sup-Lattice 𝓤 𝓥)
                      → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩), is-σ-sup-lattice-homomorphism· 𝓐 𝓑 f)
        where

\end{code}

We first introduce some abbreviations:

\begin{code}

  private
   A   = ⟨ 𝓐 ⟩
   ⊥   = ⊥⟨ 𝓐 ⟩
   ⊤   = ⊤⟨ 𝓐 ⟩
   ⋁  = ⋁⟨ 𝓐 ⟩

  _≤_ : A → A → 𝓤₀ ̇
  a ≤ b = a ≤⟨ 𝓐 ⟩ b
  ≡-gives-≤ : (a b : A) → a ≡ b → a ≤ b
  ≡-gives-≤ a b p = transport (a ≤_) p (⟨ 𝓐 ⟩-refl a)

\end{code}

\begin{code}

  σ-rec : (𝓑 : σ-Sup-Lattice 𝓤 𝓥) → ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩
  σ-rec 𝓑 = pr₁ (center (𝓐-is-initial 𝓑))

  σ-rec-is-homomorphism : (𝓑 : σ-Sup-Lattice 𝓤 𝓥)
                        → is-σ-sup-lattice-homomorphism· 𝓐 𝓑 (σ-rec 𝓑)
  σ-rec-is-homomorphism 𝓑 = pr₂ (center (𝓐-is-initial 𝓑))

  σ-rec-is-unique : (𝓑 : σ-Sup-Lattice 𝓤 𝓥)
                  → (f : A → ⟨ 𝓑 ⟩)
                  → is-σ-sup-lattice-homomorphism· 𝓐 𝓑 f
                  → σ-rec 𝓑 ≡ f
  σ-rec-is-unique 𝓑 f i = ap pr₁ (centrality (𝓐-is-initial 𝓑) (f , i))

  at-most-one-homomorphism : (𝓑 : σ-Sup-Lattice 𝓤 𝓥)
                           → (f g : A → ⟨ 𝓑 ⟩)
                           → is-σ-sup-lattice-homomorphism· 𝓐 𝓑 f
                           → is-σ-sup-lattice-homomorphism· 𝓐 𝓑 g
                           → f ≡ g
  at-most-one-homomorphism 𝓑 f g i j = ap pr₁ (singletons-are-props (𝓐-is-initial 𝓑) (f , i) (g , j))

\end{code}

We then prove an induction principle:

\begin{code}

  σ-induction : (P : A → 𝓥 ̇ )
              → ((a : A) → is-prop (P a))
              → P ⊤
              → P ⊥
              → ((a : (ℕ → A)) → ((n : ℕ) → P (a n)) → P (⋁ a))
              → (a : A) → P a
  σ-induction {𝓥} P P-is-prop-valued ⊤-closure ⊥-closure ⋁-closure = γ
   where
    X = Σ a ꞉ A , P a

    ⊤' ⊥' : X
    ⊤' = (⊤ , ⊤-closure)
    ⊥' = (⊥ , ⊥-closure)

    ⋁' : (ℕ → X) → X
    ⋁' x = (⋁ (pr₁ ∘ x) , ⋁-closure (pr₁ ∘ x) (pr₂ ∘ x))

    _≤'_ : X → X → 𝓤₀ ̇
    (a , _) ≤' (b , _) = a ≤ b

    𝓑 : σ-Sup-Lattice 𝓥 𝓤₀
    𝓑 = X , (⊤' , ⊥' , ⋁') ,
         _≤'_ ,
         (λ (a , _) (b , _) → ⟨ 𝓐 ⟩-order-is-prop-valued a b) ,
         (λ (a , _) → ⟨ 𝓐 ⟩-refl a) ,
         (λ (a , _) (b , _) (c , _) → ⟨ 𝓐 ⟩-trans a b c) ,
         (λ (a , _) (b , _) l m → to-subtype-≡ P-is-prop-valued (⟨ 𝓐 ⟩-antisym a b l m)) ,
         (λ (a , _) → ⟨ 𝓐 ⟩-⊤-maximum a) ,
         (λ (a , _) → ⟨ 𝓐 ⟩-⊥-minimum a) ,
         (λ x n → ⟨ 𝓐 ⟩-⋁-is-ub (pr₁ ∘ x) n) ,
         (λ x (u , _) φ → ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (pr₁ ∘ x) u φ)

    g : X → A
    g = pr₁

    g-is-homomorphism : is-σ-sup-lattice-homomorphism· 𝓑 𝓐 g
    g-is-homomorphism = refl , refl , (λ 𝕒 → refl)

    h : A → A
    h = g ∘ σ-rec 𝓑

    h-is-homomorphism : is-σ-sup-lattice-homomorphism· 𝓐 𝓐 h
    h-is-homomorphism = ∘-σ-sup-lattice-homomorphism· 𝓐 𝓑 𝓐
                         (σ-rec 𝓑) g (σ-rec-is-homomorphism 𝓑) g-is-homomorphism

    H : h ≡ id
    H = at-most-one-homomorphism 𝓐 h id h-is-homomorphism
          (id-is-σ-sup-lattice-homomorphism· 𝓐)

    δ : (a : A) → P (h a)
    δ a = pr₂ (σ-rec 𝓑 a)

    γ : (a : A) → P a
    γ a = transport P (happly H a) (δ a)

\end{code}

In order to show that the initial σ-sup-lattice has binary meets, we
define a sub-σ-sup-lattice for any element of the initial one, by
taking its down set:

\begin{code}

  ↓ : A → 𝓤₀ ̇
  ↓ a = Σ d ꞉ A , d ≤ a


  down : A → σ-Sup-Lattice 𝓤₀ 𝓤₀
  down t = ↓ t ,
           ((t , ⟨ 𝓐 ⟩-refl t) ,
            (⊥ , ⟨ 𝓐 ⟩-⊥-minimum t) ,
            (λ x → ⋁ (pr₁ ∘ x) , ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (pr₁ ∘ x) t (pr₂ ∘ x))) ,
           (λ (a , _)(b , _) → a ≤ b) ,
           (λ (a , _) (b , _) → ⟨ 𝓐 ⟩-order-is-prop-valued a b) ,
           (λ (a , _) → ⟨ 𝓐 ⟩-refl a) ,
           (λ (a , _) (b , _) (c , _) → ⟨ 𝓐 ⟩-trans a b c) ,
           (λ (a , _) (b , _) l m → to-subtype-≡ (λ a → ⟨ 𝓐 ⟩-order-is-prop-valued a t) (⟨ 𝓐 ⟩-antisym a b l m)) ,
           (λ (a , l) → l) ,
           (λ (a , _) → ⟨ 𝓐 ⟩-⊥-minimum a) ,
           (λ x n → ⟨ 𝓐 ⟩-⋁-is-ub (pr₁ ∘ x) n) ,
           (λ x (u , _) φ → ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (pr₁ ∘ x) u φ)
\end{code}

Then we apply initiality:

\begin{code}
  meet : (a : A) → A → ↓ a
  meet a = pr₁ (center (𝓐-is-initial (down a)))

  meet-is-homomorphism : (a : A) → is-σ-sup-lattice-homomorphism· 𝓐 (down a) (meet a)
  meet-is-homomorphism a = pr₂ (center (𝓐-is-initial (down a)))

  _∧_ : A → A → A
  a ∧ b = pr₁ (meet a b)

  infix 100 _∧_

  ∧-is-lb-left : (a b : A) → a ∧ b ≤ a
  ∧-is-lb-left a b = pr₂ (meet a b)

  meet⊤ : (a : A) → a ∧ ⊤ ≡ a
  meet⊤ a = ap pr₁ (pr₁ (meet-is-homomorphism a))

  meet⊥ : (a : A) → a ∧ ⊥ ≡ ⊥
  meet⊥ a = ap pr₁ (pr₁ (pr₂ ((meet-is-homomorphism a))))

  meet⋁ : (a : A) (b : ℕ → A) → a ∧ ⋁ b ≡ ⋁ (n ↦ a ∧ b n)
  meet⋁ a b = ap pr₁ (pr₂ (pr₂ (meet-is-homomorphism a)) b)

\end{code}

Using this, we show that a ∧ b is the greatest lower bound to a and b,
by induction:

\begin{code}

  ∧-is-lb-right : (a b : A) → a ∧ b ≤ b
  ∧-is-lb-right a = σ-induction (λ b → (a ∧ b) ≤ b)
                     (λ b → ⟨ 𝓐 ⟩-order-is-prop-valued (a ∧ b) b)
                     (⟨ 𝓐 ⟩-⊤-maximum (a ∧ ⊤))
                     (transport (_≤ ⊥) ((meet⊥ a)⁻¹) (⟨ 𝓐 ⟩-refl ⊥))
                     p
   where
    p : (c : ℕ → A)
      → ((n : ℕ) → a ∧ c n ≤ c n)
      → a ∧ ⋁ c ≤ ⋁ c
    p c φ = transport (_≤ ⋁ c) (q ⁻¹) r
     where
      q : a ∧ ⋁ c ≡ ⋁ (n ↦ a ∧ c n)
      q = meet⋁ a c
      s : (n : ℕ) → a ∧ c n ≤ ⋁ c
      s n = ⟨ 𝓐 ⟩-trans _ _ _ (φ n) (⟨ 𝓐 ⟩-⋁-is-ub c n)
      r : ⋁ (n ↦ a ∧ c n) ≤ ⋁ c
      r = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs _ _ s

  ∧-is-ub-of-lbs : (a b c : A) → c ≤ a → c ≤ b → c ≤ a ∧ b
  ∧-is-ub-of-lbs a b = σ-induction
                        (λ c → c ≤ a → c ≤ b → c ≤ a ∧ b)
                        (λ c → Π₂-is-prop fe (λ _ _ → ⟨ 𝓐 ⟩-order-is-prop-valued c (a ∧ b)))
                        p q r
   where
    p : ⊤ ≤ a → ⊤ ≤ b → ⊤ ≤ a ∧ b
    p l m = transport (⊤ ≤_) t (⟨ 𝓐 ⟩-refl ⊤)
     where
      u : ⊤ ≡ a
      u = ⟨ 𝓐 ⟩-antisym _ _ l (⟨ 𝓐 ⟩-⊤-maximum a)
      v : ⊤ ≡ b
      v = ⟨ 𝓐 ⟩-antisym _ _ m (⟨ 𝓐 ⟩-⊤-maximum b)
      w : ⊤ ≡ ⊤ ∧ ⊤
      w = (meet⊤ ⊤)⁻¹
      t : ⊤ ≡ a ∧ b
      t = w ∙ ap₂ _∧_ u v

    q : ⊥ ≤ a → ⊥ ≤ b → ⊥ ≤ a ∧ b
    q _ _ = ⟨ 𝓐 ⟩-⊥-minimum (a ∧ b)
    r : (d : ℕ → A)
      → ((n : ℕ) → d n ≤ a → d n ≤ b → d n ≤ a ∧ b)
      → ⋁ d ≤ a
      → ⋁ d ≤ b
      → ⋁ d ≤ (a ∧ b)
    r d φ l m = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs _ _
                     (λ n → φ n (⟨ 𝓐 ⟩-trans _ _ _ (⟨ 𝓐 ⟩-⋁-is-ub d n) l)
                                (⟨ 𝓐 ⟩-trans _ _ _ (⟨ 𝓐 ⟩-⋁-is-ub d n) m))
\end{code}

TODO. The following needs tidying up and comments. (And probably the above too.)

We show that the initial σ-sup-lattice is also the initial σ-frame.

\begin{code}

  ∧-idempotent : (a : A) → a ∧ a ≡ a
  ∧-idempotent a = ⟨ 𝓐 ⟩-antisym _ _ l m
   where
    l : a ∧ a ≤ a
    l = ∧-is-lb-left a a
    m : a ≤ a ∧ a
    m = ∧-is-ub-of-lbs a a a (⟨ 𝓐 ⟩-refl a) (⟨ 𝓐 ⟩-refl a)

  ∧-commutative : (a b : A) → a ∧ b ≡ b ∧ a
  ∧-commutative a b = ⟨ 𝓐 ⟩-antisym _ _ (l a b) (l b a)
   where
    l : (a b : A) → a ∧ b ≤ b ∧ a
    l a b = ∧-is-ub-of-lbs b a (a ∧ b) (∧-is-lb-right a b) (∧-is-lb-left a b)

  ∧-associative : (a b c : A) → a ∧ (b ∧ c) ≡ (a ∧ b) ∧ c
  ∧-associative a b c = ⟨ 𝓐 ⟩-antisym _ _ l m
   where
    l : a ∧ (b ∧ c) ≤ (a ∧ b) ∧ c
    l = ∧-is-ub-of-lbs _ _ _ (∧-is-ub-of-lbs _ _ _ (∧-is-lb-left a (b ∧ c)) u) v
     where
      u : a ∧ (b ∧ c) ≤ b
      u = ⟨ 𝓐 ⟩-trans _ _ _ (∧-is-lb-right  a (b ∧ c)) (∧-is-lb-left b c)
      v : a ∧ (b ∧ c) ≤ c
      v = ⟨ 𝓐 ⟩-trans _ _ _ (∧-is-lb-right a (b ∧ c)) (∧-is-lb-right b c)

    m : (a ∧ b) ∧ c ≤ a ∧ (b ∧ c)
    m = ∧-is-ub-of-lbs _ _ _ (⟨ 𝓐 ⟩-trans _ _ _ (∧-is-lb-left (a ∧ b) c) (∧-is-lb-left a b)) u
     where
      p : (a ∧ b) ∧ c ≤ b
      p = ⟨ 𝓐 ⟩-trans _ _ _ (∧-is-lb-left (a ∧ b) c) (∧-is-lb-right a b)
      u : (a ∧ b) ∧ c ≤ b ∧ c
      u = ∧-is-ub-of-lbs _ _ _ p (∧-is-lb-right (a ∧ b) c)

  from-≤ : (a b : A) → a ≤ b → a ∧ b ≡ a
  from-≤ a b l = ⟨ 𝓐 ⟩-antisym _ _ (∧-is-lb-left a b) m
   where
    m : a ≤ a ∧ b
    m = ∧-is-ub-of-lbs _ _ _ (⟨ 𝓐 ⟩-refl a) l

  to-≤ : (a b : A) → a ∧ b ≡ a → a ≤ b
  to-≤ a b p = ⟨ 𝓐 ⟩-trans _ _ _ l (∧-is-lb-right a b)
   where
    l : a ≤ a ∧ b
    l = transport (a ≤_) (p ⁻¹) (⟨ 𝓐 ⟩-refl a)

  open σ-frame hiding (order)
               renaming
                (⟨_⟩ to ⟨_⟩' ;
                 ⊥⟨_⟩ to ⊥⟨_⟩' ;
                 ⊤⟨_⟩ to ⊤⟨_⟩' ;
                 meet to meet' ;
                 ⋁⟨_⟩ to ⋁⟨_⟩' ;
                 ⟨_⟩-is-set to ⟨_⟩'-is-set ;
                 ⟨_⟩-refl to ⟨_⟩'-refl ;
                 ⟨_⟩-trans to ⟨_⟩'-trans ;
                 ⟨_⟩-antisym to ⟨_⟩'-antisym ;
                 ⟨_⟩-⊤-maximum to ⟨_⟩'-⊤-maximum ;
                 ⟨_⟩-⊥-minimum to ⟨_⟩'-⊥-minimum ;
                 ⟨_⟩-⋁-is-ub to ⟨_⟩'-⋁-is-ub ;
                 ⟨_⟩-⋁-is-lb-of-ubs to ⟨_⟩'-⋁-is-lb-of-ubs)

  𝓐-qua-σ-frame : σ-Frame 𝓤₀
  𝓐-qua-σ-frame = A , (⊤ , _∧_ , ⊥ , ⋁) ,
                   ⟨ 𝓐 ⟩-is-set ,
                   ∧-idempotent ,
                   ∧-commutative ,
                   ∧-associative ,
                   (λ a → ∧-commutative ⊥ a ∙ meet⊥ a) ,
                   meet⊤ ,
                   meet⋁ ,
                   (λ a n → from-≤ (a n) (⋁ a) (⟨ 𝓐 ⟩-⋁-is-ub a n)) ,
                   (λ a u φ → from-≤ (⋁ a) u (⟨ 𝓐 ⟩-⋁-is-lb-of-ubs a u (λ n → to-≤ (a n) u (φ n))))

  σ-frames-are-σ-sup-lattices : σ-Frame 𝓤 → σ-Sup-Lattice 𝓤 𝓤
  σ-frames-are-σ-sup-lattices 𝓑  = ⟨ 𝓑 ⟩' , (⊤⟨ 𝓑 ⟩' , ⊥⟨ 𝓑 ⟩' , ⋁⟨ 𝓑 ⟩') ,
                                          (λ x y → meet' 𝓑 x y ≡ x) ,
                                          (λ x y → ⟨ 𝓑 ⟩'-is-set) ,
                                          (⟨ 𝓑 ⟩'-refl) ,
                                          ⟨ 𝓑 ⟩'-trans ,
                                          ⟨ 𝓑 ⟩'-antisym ,
                                          ⟨ 𝓑 ⟩'-⊤-maximum ,
                                          ⟨ 𝓑 ⟩'-⊥-minimum ,
                                          ⟨ 𝓑 ⟩'-⋁-is-ub ,
                                          ⟨ 𝓑 ⟩'-⋁-is-lb-of-ubs

  𝓐-qua-σ-frame-is-initial : (𝓑 : σ-Frame 𝓤)
                            → ∃! f ꞉ (A → ⟨ 𝓑 ⟩), is-σ-frame-homomorphism· 𝓐-qua-σ-frame 𝓑 f
  𝓐-qua-σ-frame-is-initial {𝓤} 𝓑 = γ
   where
    _∧'_ : ⟨ 𝓑 ⟩ → ⟨ 𝓑 ⟩ → ⟨ 𝓑 ⟩
    _∧'_ = meet' 𝓑

    𝓑-qua-σ-sup-lattice : σ-Sup-Lattice 𝓤 𝓤
    𝓑-qua-σ-sup-lattice = σ-frames-are-σ-sup-lattices 𝓑

    f : A → ⟨ 𝓑 ⟩'
    f = pr₁ (center (𝓐-is-initial 𝓑-qua-σ-sup-lattice))

    f-is-homomorphism : is-σ-sup-lattice-homomorphism· 𝓐 𝓑-qua-σ-sup-lattice f
    f-is-homomorphism = pr₂ (center (𝓐-is-initial 𝓑-qua-σ-sup-lattice))

    f-preserves-∧ : (a b : A) → f (a ∧ b) ≡ f a ∧' f b
    f-preserves-∧ a = σ-induction (λ b → f (a ∧ b) ≡ f a ∧' f b)

                       (λ b → ⟨ 𝓑 ⟩'-is-set)
                       (f (a ∧ ⊤)       ≡⟨ ap f (meet⊤ a) ⟩
                        f a             ≡⟨ (⟨ 𝓑 ⟩'-⊤-maximum (f a))⁻¹ ⟩
                        f a ∧' ⊤⟨ 𝓑 ⟩'  ≡⟨ ap (f a ∧'_) ((sup-lattice-homomorphisms-preserve-⊤ 𝓐 𝓑-qua-σ-sup-lattice f f-is-homomorphism)⁻¹) ⟩
                        f a ∧' f ⊤      ∎)

                       (f (a ∧ ⊥)       ≡⟨ ap f (meet⊥ a) ⟩
                        f ⊥             ≡⟨ sup-lattice-homomorphisms-preserve-⊥ 𝓐 𝓑-qua-σ-sup-lattice f f-is-homomorphism ⟩
                        ⊥⟨ 𝓑 ⟩'         ≡⟨ (⟨ 𝓑 ⟩'-⊥-minimum (f a))⁻¹ ⟩
                        ⊥⟨ 𝓑 ⟩' ∧' f a  ≡⟨ ap (λ - → - ∧' f a) ((pr₁ (pr₂ f-is-homomorphism))⁻¹) ⟩
                        f ⊥ ∧' f a      ≡⟨ ⟨ 𝓑 ⟩-commutativity (f ⊥) (f a) ⟩
                        f a ∧' f ⊥      ∎)

                       (λ c p → f (a ∧ ⋁ c) ≡⟨ ap f (meet⋁ a c) ⟩
                                f (⋁ (n ↦ a ∧ c n))            ≡⟨ pr₂ (pr₂ f-is-homomorphism) (λ n → a ∧ c n) ⟩
                                ⋁⟨ 𝓑 ⟩' (n ↦ f (a ∧ c n))      ≡⟨ ap ⋁⟨ 𝓑 ⟩' (dfunext fe p) ⟩
                                ⋁⟨ 𝓑 ⟩' (n ↦ f a ∧' f (c n))   ≡⟨ (⟨ 𝓑 ⟩-distributivity (f a) (λ n → f (c n)))⁻¹ ⟩
                                f a ∧' ⋁⟨ 𝓑 ⟩' (λ n → f (c n)) ≡⟨ ap (f a ∧'_) ((sup-lattice-homomorphisms-preserve-⋁ 𝓐 𝓑-qua-σ-sup-lattice f
                                                                                   f-is-homomorphism c)⁻¹) ⟩
                                f a ∧' f (⋁ c)                 ∎)

    f-is-homomorphism' : is-σ-frame-homomorphism· 𝓐-qua-σ-frame 𝓑 f
    f-is-homomorphism' = sup-lattice-homomorphisms-preserve-⊤ 𝓐 𝓑-qua-σ-sup-lattice f f-is-homomorphism ,
                         f-preserves-∧ ,
                         sup-lattice-homomorphisms-preserve-⊥ 𝓐 𝓑-qua-σ-sup-lattice f f-is-homomorphism ,
                         sup-lattice-homomorphisms-preserve-⋁ 𝓐 𝓑-qua-σ-sup-lattice f f-is-homomorphism

    forget : (g : A → ⟨ 𝓑 ⟩') → is-σ-frame-homomorphism· 𝓐-qua-σ-frame 𝓑 g
                              →  is-σ-sup-lattice-homomorphism· 𝓐 𝓑-qua-σ-sup-lattice g
    forget g (i , ii , iii , vi) = (i , iii , vi)

    uniqueness : (g : A → ⟨ 𝓑 ⟩') → is-σ-frame-homomorphism· 𝓐-qua-σ-frame 𝓑 g → f ≡ g
    uniqueness g g-is-homomorphism' = ap pr₁ (singletons-are-props
                                               (𝓐-is-initial 𝓑-qua-σ-sup-lattice)
                                               (f , f-is-homomorphism)
                                               (g , forget g g-is-homomorphism'))

    γ : ∃! f ꞉ (A → ⟨ 𝓑 ⟩), is-σ-frame-homomorphism· 𝓐-qua-σ-frame 𝓑 f
    γ = (f , f-is-homomorphism') ,
        (λ (g , g-is-homomorphism') → to-subtype-≡
                                      (being-σ-frame-homomorphism·-is-prop fe 𝓐-qua-σ-frame 𝓑)
                                      (uniqueness g g-is-homomorphism'))

  σΩ : σ-Sup-Lattice 𝓤₁ 𝓤₁
  σΩ = σ-frames-are-σ-sup-lattices Ω-is-σ-frame.σΩ

  ⊥'   = ⊥⟨ σΩ ⟩
  ⊤'   = ⊤⟨ σΩ ⟩
  ⋁'  = ⋁⟨ σΩ ⟩
  _≤'_ : Ω 𝓤₀ → Ω 𝓤₀ → (𝓤₀ ⁺) ̇
  x ≤' y = x ≤⟨ σΩ ⟩ y

  ≡-gives-≤' : (p q : Ω 𝓤₀) → p ≡ q → p ≤' q
  ≡-gives-≤' p q r = transport (p ≤'_) r (⟨ σΩ ⟩-refl p)

  τ : A → Ω 𝓤₀
  τ = σ-rec σΩ

  τ-hom  : is-σ-sup-lattice-homomorphism· 𝓐 σΩ τ
  τ-hom = σ-rec-is-homomorphism σΩ

  τ-reflects-⊤ : (a : A) → τ a ≡ ⊤' → a ≡ ⊤
  τ-reflects-⊤ = σ-induction
                  (λ a → τ a ≡ ⊤' → a ≡ ⊤)
                  (λ a → Π-is-prop fe (λ _ → ⟨ 𝓐 ⟩-is-set)) i⊤ i⊥ i⋁
   where
    i⊤ : τ ⊤ ≡ ⊤' → ⊤ ≡ ⊤
    i⊤ _ = refl

    i⊥ : τ ⊥ ≡ ⊤' → ⊥ ≡ ⊤
    i⊥ p = unique-from-𝟘 (𝟘-is-not-𝟙 r)
     where
      q : ⊥' ≡ ⊤'
      q = (sup-lattice-homomorphisms-preserve-⊥ 𝓐 σΩ τ τ-hom)⁻¹ ∙ p

      r : 𝟘 ≡ 𝟙
      r = ap _holds q

    i⋁ : (a : ℕ → A) → ((n : ℕ) → τ (a n) ≡ ⊤' → a n ≡ ⊤) → τ (⋁ a) ≡ ⊤' → ⋁ a ≡ ⊤
    i⋁ a φ p = ∥∥-rec ⟨ 𝓐 ⟩-is-set iii ii
     where
      i : ⋁' (τ ∘ a) ≡ ⊤'
      i = (sup-lattice-homomorphisms-preserve-⋁ 𝓐 σΩ τ τ-hom a)⁻¹ ∙ p

      ii : ∃ n ꞉ ℕ , τ (a n) holds
      ii = equal-⊤-gives-holds (⋁' (τ ∘ a)) i

      iii : (Σ n ꞉ ℕ , τ (a n) holds) → ⋁ a ≡ ⊤
      iii (n , h) = vii
       where
        iv : τ (a n) ≡ ⊤'
        iv = holds-gives-equal-⊤ pe fe (τ (a n)) h

        v : a n ≡ ⊤
        v = φ n iv

        vi : ⊤ ≤ ⋁ a
        vi = transport (_≤ ⋁ a) v (⟨ 𝓐 ⟩-⋁-is-ub a n)

        vii : ⋁ a ≡ ⊤
        vii = ⟨ 𝓐 ⟩-antisym _ _ (⟨ 𝓐 ⟩-⊤-maximum (⋁ a)) vi
\end{code}

A frame is called compact if every open cover of its top element has a
finite subcover. It is supercompact (I think the terminology is due to
Isbell) if every cover of the top element has a singleton
subcover. This motivates the name of the following theorem, whose
crucial ingredient is the homomorphism τ and the fact that it reflects
top elements.

\begin{code}

  𝓐-is-σ-super-compact : (a : ℕ → A) → ⋁ a ≡ ⊤ → ∃ n ꞉ ℕ , a n ≡ ⊤
  𝓐-is-σ-super-compact a p = vi
   where
    i : ⋁' (τ ∘ a) ≡ ⊤'
    i = ⋁' (τ ∘ a) ≡⟨ (sup-lattice-homomorphisms-preserve-⋁ 𝓐 σΩ τ τ-hom a)⁻¹ ⟩
        τ (⋁ a)    ≡⟨ ap τ p ⟩
        τ ⊤        ≡⟨ sup-lattice-homomorphisms-preserve-⊤ 𝓐 σΩ τ τ-hom ⟩
        ⊤'         ∎

    ii : (∃ n ꞉ ℕ , τ (a n) holds) ≡ 𝟙
    ii = ap _holds i

    iii : (Σ n ꞉ ℕ , τ (a n) holds) → (Σ n ꞉ ℕ , a n ≡ ⊤)
    iii (n , h) = n , v
     where
      iv : τ (a n) ≡ ⊤'
      iv = holds-gives-equal-⊤ pe fe (τ (a n)) h

      v : a n ≡ ⊤
      v = τ-reflects-⊤ (a n) iv

    vi : ∃ n ꞉ ℕ , a n ≡ ⊤
    vi = ∥∥-functor iii (equal-𝟙-gives-holds (∃ n ꞉ ℕ , τ (a n) holds) ii)

  τ-charac→ : (a : A) → τ a holds → a ≡ ⊤
  τ-charac→ a h = τ-reflects-⊤ a (holds-gives-equal-⊤ pe fe (τ a) h)

  τ-charac← : (a : A) → a ≡ ⊤ → τ a holds
  τ-charac← a p = equal-⊤-gives-holds (τ a)
                   (τ a ≡⟨ ap τ p ⟩
                    τ ⊤ ≡⟨ sup-lattice-homomorphisms-preserve-⊤ 𝓐 σΩ τ τ-hom ⟩
                    ⊤' ∎)

  τ-charac : (a : A) → τ a ≡ ((a ≡ ⊤) , ⟨ 𝓐 ⟩-is-set)
  τ-charac a = to-subtype-≡ (λ a → being-prop-is-prop fe)
                (pe (holds-is-prop (τ a)) ⟨ 𝓐 ⟩-is-set (τ-charac→ a) (τ-charac← a))

  non-trivial : ⊥ ≢ ⊤
  non-trivial p = ⊥-is-not-⊤ q
   where
    q : ⊥' ≡ ⊤'
    q = ⊥' ≡⟨ (sup-lattice-homomorphisms-preserve-⊥ 𝓐 σΩ τ τ-hom)⁻¹ ⟩
        τ ⊥ ≡⟨ ap τ p ⟩
        τ ⊤ ≡⟨ sup-lattice-homomorphisms-preserve-⊤ 𝓐 σΩ τ τ-hom ⟩
        ⊤' ∎

  order-charac : (a b : A) → (a ≡ ⊤ → b ≡ ⊤) → a ≤ b
  order-charac = σ-induction
                 (λ a → (b : A) → (a ≡ ⊤ → b ≡ ⊤) → a ≤ b)
                 (λ a → Π₂-is-prop fe (λ b _ → ⟨ 𝓐 ⟩-order-is-prop-valued a b))
                 i⊤
                 i⊥
                 i⋁
   where
    i⊤ : (b : A) → (⊤ ≡ ⊤ → b ≡ ⊤) → ⊤ ≤ b
    i⊤ b f = ≡-gives-≤ ⊤ b ((f refl)⁻¹)

    i⊥ : (b : A) → (⊥ ≡ ⊤ → b ≡ ⊤) → ⊥ ≤ b
    i⊥ b _ = ⟨ 𝓐 ⟩-⊥-minimum b

    i⋁ : (a : ℕ → A)
       → ((n : ℕ) (b : A) → (a n ≡ ⊤ → b ≡ ⊤) → a n ≤ b)
       → (b : A)
       → (⋁ a ≡ ⊤ → b ≡ ⊤)
       → ⋁ a ≤ b
    i⋁ a φ b ψ = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs a b
                      (λ n → φ n b
                               (λ (p : a n ≡ ⊤) → ψ (f n p)))
     where
      f : (n : ℕ) → a n ≡ ⊤ → ⋁ a ≡ ⊤
      f n p = ⟨ 𝓐 ⟩-antisym _ _ (⟨ 𝓐 ⟩-⊤-maximum (⋁ a)) l
       where
        l : ⊤ ≤ ⋁ a
        l = ⟨ 𝓐 ⟩-trans _ _ _ (≡-gives-≤ ⊤ (a n) (p ⁻¹)) (⟨ 𝓐 ⟩-⋁-is-ub a n)

  τ-order-lc : (a b : A) → τ a ≤' τ b → a ≤ b
  τ-order-lc a b l = iv
   where
    i : τ a holds → τ b holds
    i = Ω-is-σ-frame.from-≤Ω {𝓤₀} {τ a} {τ b} l

    ii : τ a ≡ ⊤' → τ b ≡ ⊤'
    ii p = holds-gives-equal-⊤ pe fe (τ b) (i (equal-⊤-gives-holds (τ a) p))

    iii : a ≡ ⊤ → b ≡ ⊤
    iii q = τ-reflects-⊤ b (ii r)
     where
      r = τ a ≡⟨ ap τ q ⟩
          τ ⊤ ≡⟨ sup-lattice-homomorphisms-preserve-⊤ 𝓐 σΩ τ τ-hom ⟩
          ⊤' ∎

    iv : a ≤ b
    iv = order-charac a b iii

  τ-lc : left-cancellable τ
  τ-lc {a} {b} p = ⟨ 𝓐 ⟩-antisym a b l r
   where
    l : a ≤ b
    l = τ-order-lc a b (≡-gives-≤' (τ a) (τ b) p)

    r : b ≤ a
    r = τ-order-lc b a (≡-gives-≤' (τ b) (τ a) (p ⁻¹))

  τ-is-embedding : is-embedding τ
  τ-is-embedding = lc-maps-into-sets-are-embeddings τ τ-lc (Ω-is-set fe pe)

  holds-is-embedding : is-embedding (_holds {𝓤})
  holds-is-embedding = pr₁-is-embedding (λ _ → being-prop-is-prop fe)

  Q : A → 𝓤₀ ̇
  Q a = τ a holds

  Q-is-embedding : is-embedding Q
  Q-is-embedding = ∘-is-embedding τ-is-embedding holds-is-embedding

  is-quasidecidable : 𝓤₀ ̇ → 𝓤₁ ̇
  is-quasidecidable = fiber Q

  being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P)
  being-quasidecidable-is-prop = Q-is-embedding

  quasidecidable-types-are-props : ∀ P → is-quasidecidable P → is-prop P
  quasidecidable-types-are-props P (a , p) = transport is-prop p (holds-is-prop (τ a))

  𝟘-is-quasidecidable : is-quasidecidable 𝟘
  𝟘-is-quasidecidable = ⊥ , ap _holds (sup-lattice-homomorphisms-preserve-⊥ 𝓐 σΩ τ τ-hom)

  𝟙-is-quasidecidable : is-quasidecidable 𝟙
  𝟙-is-quasidecidable = ⊤ , ap _holds (sup-lattice-homomorphisms-preserve-⊤ 𝓐 σΩ τ τ-hom)

  quasidecidable-closed-under-ω-joins :
     (P : ℕ → 𝓤₀ ̇ )
   → ((n : ℕ) → is-quasidecidable (P n))
   → is-quasidecidable (∃ n ꞉ ℕ , P n)
  quasidecidable-closed-under-ω-joins P φ = ⋁ (n ↦ fiber-point (φ n)) , vi
   where
    i : (n : ℕ) → Q (fiber-point (φ n)) ≡ P n
    i n = fiber-identification (φ n)

    ii : (n : ℕ) → τ (fiber-point (φ n)) ≡ P n , quasidecidable-types-are-props (P n) (φ n)
    ii n = to-subtype-≡ (λ _ → being-prop-is-prop fe) (i n)

    iii : τ (⋁ (n ↦ fiber-point (φ n))) ≡ ⋁' (λ n → P n , quasidecidable-types-are-props (P n) (φ n))
    iii = τ (⋁ (n ↦ fiber-point (φ n)))                               ≡⟨ iv ⟩
          ⋁' (n ↦ τ (fiber-point (φ n)))                              ≡⟨ v  ⟩
          ⋁' (n ↦ (P n , quasidecidable-types-are-props (P n) (φ n))) ∎
     where
      iv = sup-lattice-homomorphisms-preserve-⋁ 𝓐 σΩ τ τ-hom (λ n → fiber-point (φ n))
      v  = ap ⋁' (dfunext fe ii)

    vi : Q (⋁ (n ↦ fiber-point (φ n))) ≡ (∃ n ꞉ ℕ , P n)
    vi = ap _holds iii

  quasidecidable-induction :
     (F : 𝓤₀ ̇ → 𝓤 ̇ )
   → ((P : 𝓤₀ ̇ ) → is-prop (F P))
   → F 𝟘
   → F 𝟙
   → ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
   → (P : 𝓤₀ ̇ ) → is-quasidecidable P → F P
  quasidecidable-induction F i F₀ F₁ Fω P (a , r) = γ a P r
   where
    γ : (a : A) (P : 𝓤₀ ̇ ) → τ a holds ≡ P → F P
    γ = σ-induction {!!} {!!} γ⊤ γ⊥ γ⋁
{-    γ : (a : A) → τ a holds ≡ P → F P
    γ = σ-induction (λ a → τ a holds ≡ P → F P) (λ a → Π-is-prop fe (λ _ → i P))
         γ⊤ γ⊥ γ⋁
-}
     where
      γ⊤ : (P : 𝓤₀ ̇ ) → τ ⊤ holds ≡ P → F P
      γ⊤ P s = transport F (t ⁻¹ ∙ s) F₁
       where
        t : τ ⊤ holds ≡ 𝟙
        t = ap _holds (sup-lattice-homomorphisms-preserve-⊤ 𝓐 σΩ τ τ-hom)
      γ⊥ : (P : 𝓤₀ ̇ ) → τ ⊥ holds ≡ P → F P
      γ⊥ P s = transport F (t ⁻¹ ∙ s) F₀
       where
        t : τ ⊥ holds ≡ 𝟘
        t = ap _holds (sup-lattice-homomorphisms-preserve-⊥ 𝓐 σΩ τ τ-hom)

      γ⋁ : (a : ℕ → A)
         → ((n : ℕ) (P : 𝓤₀ ̇) → (τ (a n) holds) ≡ P → F P)
         → (P : 𝓤₀ ̇) → (τ (⋁ a) holds) ≡ P → F P
      γ⋁ a φ P s = transport F (t ⁻¹ ∙ s) (Fω (λ n → τ (a n) holds) ψ)
       where
        t : τ (⋁ a) holds ≡ (∃ n ꞉ ℕ , τ (a n) holds)
        t = ap _holds (sup-lattice-homomorphisms-preserve-⋁ 𝓐 σΩ τ τ-hom a)
        ψ : (n : ℕ) → F (τ (a n) holds)
        ψ n = φ n (τ (a n) holds) refl




{- Use 𝓐-is-σ-super-compact to complete this easily:

  M : (a : A) (b : a ≡ ⊤ → A)
                     → Σ m ꞉ A , ((p : a ≡ ⊤) → m ≤ b p)
                               × ((l : A) → ((p : a ≡ ⊤) → l ≤ b p) → l ≤ m)
  M = σ-induction P P-is-prop-valued M⊤ M⊥ M⋁
   where
    P : A → {!!} ̇
    P a = (b : a ≡ ⊤ → A) → Σ m ꞉ A , ((p : a ≡ ⊤) → m ≤ b p) × ((l : A) → ((p : a ≡ ⊤) → l ≤ b p) → l ≤ m)
    P-is-prop-valued : (a : A) → is-prop (P a)
    P-is-prop-valued a = {!!}
    M⊤ : (b : ⊤ ≡ ⊤ → A) → Σ m ꞉ A , ((p : ⊤ ≡ ⊤) → m ≤ b p) × ((l : A) → ((p : ⊤ ≡ ⊤) → l ≤ b p) → l ≤ m)
    M⊤ b = {!!}
    M⊥ : (b : ⊥ ≡ ⊤ → A) → Σ m ꞉ A , ((p : ⊥ ≡ ⊤) → m ≤ b p) × ((l : A) → ((p : ⊥ ≡ ⊤) → l ≤ b p) → l ≤ m)
    M⊥ b = {!!}
    M⋁ : (c : ℕ → A) → ((n : ℕ) → P (c n)) → P (⋁ c)
    M⋁ c φ b = ⋁ m , γ₁ , γ₂
     where
      u : (n : ℕ) → c n ≡ ⊤ → ⋁ c ≡ ⊤
      u n q = {!!}
      σ-compact : ⊤ ≤ ⋁ c → Σ n ꞉ ℕ , ⊤ ≤ c n
      σ-compact l = {!!}
      d : ⋁ c ≡ ⊤ → Σ n ꞉ ℕ , c n ≡ ⊤
      d p = {!!}

      m : ℕ → A
      m n = pr₁ (φ n (λ q → b (u n q)))

      φ₁ : (n : ℕ) → (p : c n ≡ ⊤) → m n ≤ b (u n p)
      φ₁ n = pr₁ (pr₂ (φ n (λ q → b (u n q))))

      φ₂ : (n : ℕ) (l : A) → ((p : c n ≡ ⊤) → l ≤ b (u n p)) → l ≤ m n
      φ₂ n = pr₂ (pr₂ (φ n (λ q → b (u n q))))

      γ₁ : (p : ⋁ c ≡ ⊤) → ⋁ m ≤ b p
      γ₁ = {!!}

      γ₂ : (l : A) → ((p : ⋁ c ≡ ⊤) → l ≤ b p) → l ≤ ⋁ m
      γ₂ = {!!}
-}

\end{code}

To be continued.
