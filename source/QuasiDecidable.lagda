Martin Escardo, May 2020.

The quasidecidable propositions generalize the semidecidable
propositions.  A weakening of the axiom of countable choice is
equivalent to the equivalence of semidecidability with
quasidecidability.

The quasidecidable propositions form a dominance, and their totality
defines the initial σ-frame.  A σ-frame is a poset with countable
joins and finite meets such that binary meets distribute over
countable joins.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import GenericConvergentSequence
open import UF-PropTrunc
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-EquivalenceExamples
open import UF-Yoneda
open import Dominance
open import UF-SIP
open import UF-SIP-Examples

module QuasiDecidable where

\end{code}

A proposition is semidecidable if it is a countable join of decidable
propositions. See the
paperhttps://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf
by Martin Escardo and Cory Knapp.

\begin{code}
module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-semidecidable : 𝓤 ̇ → 𝓤 ̇
 is-semidecidable X = ∃ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

\end{code}

The following shows that we need to truncate, because the Cantor
(ℕ → 𝟚) is certainly not the type of semi-decidable propositions:

\begin{code}
 semidecidability-data : 𝓤 ̇ → 𝓤 ̇
 semidecidability-data X = Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)

 totality-of-semidecidability-data : is-univalent 𝓤₀
                                   → (Σ X ꞉ 𝓤₀ ̇ , semidecidability-data X) ≃ (ℕ → 𝟚)
 totality-of-semidecidability-data ua =

   (Σ X ꞉ 𝓤₀ ̇ , Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)) ≃⟨ i ⟩
   (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , X ≃ (∃ n ꞉ ℕ , α n ≡ ₁)) ≃⟨ ii ⟩
   (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , (∃ n ꞉ ℕ , α n ≡ ₁) ≃ X) ≃⟨ iii ⟩
   (ℕ → 𝟚) × 𝟙 {𝓤₀}                                     ≃⟨ iv ⟩
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

\begin{code}

 𝟘-𝟙-ω-closed : (𝓤₀ ̇ → 𝓤 ̇ ) → 𝓤₁ ⊔ 𝓤 ̇
 𝟘-𝟙-ω-closed {𝓤} A =
     A 𝟘
   × A 𝟙
   × ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → A (P n)) → A (∃ n ꞉ ℕ , P n))

\end{code}

We assume that it exists in the following:

\begin{code}

 module _ (is-quasidecidable : 𝓤₀ ̇ → 𝓤₀ ̇ )
          (being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P))
          (𝟘-𝟙-ω-closure : 𝟘-𝟙-ω-closed is-quasidecidable)
          (quasidecidable-induction : ∀ {𝓤} (A : 𝓤₀ ̇ → 𝓤 ̇ ) → 𝟘-𝟙-ω-closed A → (P : 𝓤₀ ̇ ) → is-quasidecidable P → A P)
      where

  quasidecidable₀ : is-quasidecidable 𝟘
  quasidecidable₀ = pr₁ 𝟘-𝟙-ω-closure

  quasidecidable₁ : is-quasidecidable 𝟙
  quasidecidable₁ = pr₁ (pr₂ 𝟘-𝟙-ω-closure)

  quasidecidableω : ((P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → is-quasidecidable (P n)) → is-quasidecidable (∃ n ꞉ ℕ , P n))
  quasidecidableω = pr₂ (pr₂ 𝟘-𝟙-ω-closure)

  quasidecidable-types-are-props : ∀ P → is-quasidecidable P → is-prop P
  quasidecidable-types-are-props = quasidecidable-induction is-prop (𝟘-is-prop , 𝟙-is-prop , λ P φ → ∃-is-prop)

  quasidecidable-dom : propext 𝓤₀
                      → (P : 𝓤₀ ̇ )
                      → is-quasidecidable P
                      → (Q : 𝓤₀ ̇)
                      → (P → is-quasidecidable Q)
                      → is-quasidecidable (P × Q)
  quasidecidable-dom pe = quasidecidable-induction A (a₀ , a₁ , aω)
   where
    A : 𝓤₀ ̇ → 𝓤₁ ̇
    A P = (Q : 𝓤₀ ̇) → (P → is-quasidecidable Q) → is-quasidecidable (P × Q)
    a₀ : A 𝟘
    a₀ Q φ = transport is-quasidecidable aa quasidecidable₀
     where
      aa : 𝟘 ≡ 𝟘 × Q
      aa = pe 𝟘-is-prop (λ (z , q) → 𝟘-elim z) unique-from-𝟘 pr₁
    a₁ : A 𝟙
    a₁ Q φ = transport is-quasidecidable aa (φ *)
     where
      i : is-prop Q
      i = quasidecidable-types-are-props Q (φ *)
      aa : Q ≡ 𝟙 × Q
      aa = pe i (×-is-prop 𝟙-is-prop i) (λ q → (* , q)) pr₂
    aω :  (P : ℕ → 𝓤₀ ̇ ) → ((n : ℕ) → A (P n)) → A (∃ n ꞉ ℕ , P n)
    aω P f Q φ = γ
     where
      φ' : (n : ℕ) → P n → is-quasidecidable Q
      φ' n p = φ ∣ n , p ∣
      γ' : (n : ℕ) → is-quasidecidable (P n × Q)
      γ' n = f n Q (φ' n)
      δ : is-quasidecidable (∃ n ꞉ ℕ , P n × Q)
      δ = quasidecidableω (λ n → P n × Q) γ'
      u : (∃ n ꞉ ℕ , P n × Q) → ((∃ n ꞉ ℕ , P n) × Q)
      u s = (t , q)
       where
        t : ∃ n ꞉ ℕ , P n
        t = ∥∥-rec ∃-is-prop (λ (n , (p , q)) → ∣ n , p ∣) s
        i : is-prop Q
        i = quasidecidable-types-are-props Q (φ t)
        q : Q
        q = ∥∥-rec i (λ (n , (p , q)) → q) s
      v : ((∃ n ꞉ ℕ , P n) × Q) → (∃ n ꞉ ℕ , P n × Q)
      v (t , q) = ∥∥-functor (λ (n , p) → n , (p , q)) t
      γ : is-quasidecidable ((∃ n ꞉ ℕ , P n) × Q)
      γ = transport is-quasidecidable (pe ∃-is-prop (×-prop-criterion ((λ _ → ∃-is-prop) , (λ e → quasidecidable-types-are-props Q (φ e)))) u v) δ

  quasidecidable-closed-under-Σ : propext 𝓤₀
                                 → (P : 𝓤₀ ̇ )
                                 → is-quasidecidable P
                                 → (Q : P → 𝓤₀ ̇ )
                                 → ((p : P) → is-quasidecidable (Q p))
                                 → is-quasidecidable (Σ Q)
  quasidecidable-closed-under-Σ pe P i Q = γ
   where
    γ : ((p : P) → is-quasidecidable (Q p)) → is-quasidecidable (Σ Q)
    γ = D3-and-D5'-give-D5 pe is-quasidecidable
         quasidecidable-types-are-props
         (λ P Q' i j → quasidecidable-dom pe P i Q' j) P Q i

\end{code}

In summary, the quasidecidable properties form a dominance:

\begin{code}

  quasidecidability-is-dominance : propext 𝓤₀ → is-dominance is-quasidecidable
  quasidecidability-is-dominance pe = being-quasidecidable-is-prop ,
                                      quasidecidable-types-are-props ,
                                      quasidecidable₁ ,
                                      (λ P Q i → quasidecidable-closed-under-Σ pe P i Q)
\end{code}

We know show that binary meets (cartesian products) or quasidecidable
properties distribute over countable joins (existential
quantifications over ℕ):

\begin{code}

  quasidecidable-σ-frame-trivial :
             (P : 𝓤₀ ̇ )
           → is-quasidecidable P
           → (Q : ℕ → 𝓤₀ ̇)
           → ((n : ℕ) → is-quasidecidable (Q n))
           → P × ∃ Q → ∃ n ꞉ ℕ , P × Q n
  quasidecidable-σ-frame-trivial P i Q φ (p , e) = ∥∥-rec ∃-is-prop (λ (n , q) → ∣ n , p , q ∣) e


  quasidecidable-σ-frame-non-trivial :
             (P : 𝓤₀ ̇ )
           → is-quasidecidable P
           → (Q : ℕ → 𝓤₀ ̇)
           → ((n : ℕ) → is-quasidecidable (Q n))
           → (∃ n ꞉ ℕ , P × Q n) → P × ∃ Q
  quasidecidable-σ-frame-non-trivial = quasidecidable-induction A (a₀ , a₁ , aω)
   where
    A : 𝓤₀ ̇ → 𝓤₁ ̇
    A P = (Q : ℕ → 𝓤₀ ̇)
        → ((n : ℕ) → is-quasidecidable (Q n))
        → (∃ n ꞉ ℕ , P × Q n) → P × ∃ Q
    a₀ : A 𝟘
    a₀ Q φ e = 𝟘-elim (∥∥-rec 𝟘-is-prop (λ (n , z , q) → z) e)
    a₁ : A 𝟙
    a₁ Q φ e = * , (∥∥-rec ∃-is-prop (λ (n , o , q) → ∣ n , q ∣) e)
    aω : (P : ℕ → 𝓤₀ ̇) → ((n : ℕ) → A (P n)) → A (∃ P)
    aω P f Q φ e = ∥∥-rec ∃-is-prop (λ (n , ep , q) → ep) e , ∥∥-rec ∃-is-prop ((λ (n , ep , q) → ∣ n , q ∣)) e

  quasidecidable-σ-frame : propext 𝓤₀
           → (P : 𝓤₀ ̇ )
           → is-quasidecidable P
           → (Q : ℕ → 𝓤₀ ̇)
           → ((n : ℕ) → is-quasidecidable (Q n))
           → (∃ n ꞉ ℕ , P × Q n) ≡ P × ∃ Q
  quasidecidable-σ-frame pe P i Q φ = pe ∃-is-prop
                               (×-is-prop (quasidecidable-types-are-props P i) (quasidecidable-types-are-props (∃ Q) (quasidecidableω Q φ)))
                               (quasidecidable-σ-frame-non-trivial P i Q φ)
                               (quasidecidable-σ-frame-trivial P i Q φ)

\end{code}

We now define σ-frames.

\begin{code}

σ-frame-structure : 𝓤 ̇ → 𝓤 ̇
σ-frame-structure X = X × (X → X → X) × ((ℕ → X) → X)

σ-frame-axioms : (X : 𝓤 ̇ ) → σ-frame-structure X → 𝓤 ̇
σ-frame-axioms {𝓤} X (⊤ , _∧_ , ⋁) = I × II × III × IV × V × VI × VII
 where
  I   = is-set X
  II  = (x : X) → x ∧ x ≡ x
  III = (x y : X) → x ∧ y ≡ y ∧ x
  IV  = (x y z : X) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
  V   = (x : X) → x ∧ ⊤ ≡ x
  VI  = (x : X) (𝕪 : ℕ → X) → x ∧ (⋁ 𝕪) ≡ ⋁ (i ↦ (x ∧ 𝕪 i))
  _≤_ : X → X → 𝓤 ̇
  x ≤ y = x ∧ y ≡ x
  VII = (𝕪 : ℕ → X)
      → ((i : ℕ) → 𝕪 i ≤ ⋁ 𝕪)
      × ((u : X) → ((i : ℕ) → 𝕪 i ≤ ⋁ 𝕪) → ⋁ 𝕪 ≤ u)

σ-frame-axioms-is-prop : funext 𝓤 𝓤 → funext 𝓤₀ 𝓤
                       → (X : 𝓤 ̇ ) (s : σ-frame-structure X)
                       → is-prop (σ-frame-axioms X s)
σ-frame-axioms-is-prop fe fe₀ X (⊤ , _∧_ , ⋁) = prop-criterion δ
 where
  δ : σ-frame-axioms X (⊤ , _∧_ , ⋁) → is-prop (σ-frame-axioms X (⊤ , _∧_ , ⋁))
  δ (i , ii , iii , iv , v , vi) =
    ×-is-prop (being-set-is-prop fe)
   (×-is-prop (Π-is-prop fe (λ x →                                                   i {x ∧ x} {x}))
   (×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y →                               i {x ∧ y} {y ∧ x})))
   (×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y → Π-is-prop fe (λ z →           i {x ∧ (y ∧ z)} {(x ∧ y) ∧ z}))))
   (×-is-prop (Π-is-prop fe (λ x →                                                   i {x ∧ ⊤} {x}))
   (×-is-prop (Π-is-prop fe (λ x → Π-is-prop fe (λ y →                               i {x ∧ ⋁ y} {⋁ (i ↦ x ∧ y i)})))
              (Π-is-prop fe λ 𝕪 → ×-is-prop (Π-is-prop fe₀ (λ n →                    i {𝕪 n ∧ ⋁ 𝕪} {𝕪 n}))
                                            (Π-is-prop fe (λ x → Π-is-prop fe (λ _ → i {⋁ 𝕪 ∧ x} {⋁ 𝕪})))))))))

σ-Frame : (𝓤 : Universe) → 𝓤 ⁺ ̇
σ-Frame 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ σ-frame-structure A , σ-frame-axioms A s

_≅[σ-Frame]_ : σ-Frame 𝓤 → σ-Frame 𝓤 → 𝓤 ̇
(A , (⊤ , _∧_ , ⋁) , _) ≅[σ-Frame] (A' , (⊤' , _∧'_ , ⋁') , _) =

                        Σ f ꞉ (A → A')
                            , is-equiv f
                            × (f ⊤ ≡ ⊤')
                            × ((λ a b → f (a ∧ b)) ≡ (λ a b → f a ∧' f b))
                            × ((λ 𝕒 → f (⋁ 𝕒)) ≡ (λ 𝕒 → ⋁' (i ↦ f (𝕒 i))))
\end{code}

TODO: is-univalent 𝓤 implies funext 𝓤₀ 𝓤 because funext 𝓤 𝓤 implies
funext 𝓤₀ 𝓤 (see MGS lecture notes for a proof). Hence the assumption
funext 𝓤₀ 𝓤 is superflous in the following.

\begin{code}

characterization-of-σ-Frame-≡ : is-univalent 𝓤
                              → funext 𝓤₀ 𝓤
                              → (A B : σ-Frame 𝓤)
                              → (A ≡ B) ≃ (A ≅[σ-Frame] B)
characterization-of-σ-Frame-≡ ua fe₀ =
  sip.characterization-of-≡ ua
   (sip-with-axioms.add-axioms
      σ-frame-axioms
      (σ-frame-axioms-is-prop (univalence-gives-funext ua) fe₀)
     (sip-join.join
       pointed-type-identity.sns-data
     (sip-join.join
       ∞-magma-identity.sns-data
      (∞-bigmagma-identity.sns-data ℕ))))
\end{code}

To be continued.
