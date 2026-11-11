// Original, small question-and-answer lessons. Each file stands on its own.
export const lessons = [
  {
    id:'values', title:'A value, please', topic:'Functions',
    lead:'You know functions. Let us start with one, and ask Lean to run it.',
    question:'What will twice 7 return? Does running it tell us what happens for every number?',
    answer:'It returns 14. That is one computation. A hundred more computations would still leave infinitely many natural numbers untried.',
    source:`def twice (n : Nat) : Nat := n + n

#eval twice 7
#check twice
`,
    tryIt:'Change 7. Then change the function. Notice that #eval asks for a value, while #check asks for a type.',
    takeaway:'Nat means natural numbers: 0, 1, 2, … . A function of type Nat → Nat takes a natural number and returns one.',
  },
  {
    id:'claims', title:'A claim has a type', topic:'Propositions',
    lead:'Now ask for more than an answer. Ask for a reason that an answer is right.',
    question:'Can an equation be the type of something?',
    answer:'Yes. 2 + 2 = 4 is a proposition. A term with that type is a proof of the equation. Lean checks proof terms much as it checks the types of programs.',
    source:`#check (2 + 2 = 4)

theorem four : 2 + 2 = 4 := by
  rfl

#check four
`,
    tryIt:'Replace 4 by 5 in the theorem. Run it. Then restore it. The name four is just a name; the statement after the colon is what matters.',
    takeaway:'Prop is the type of propositions. rfl closes an equality when the two sides reduce to the same expression. It is not a general equation solver.',
  },
  {
    id:'rejection', title:'A useful “no”', topic:'Reading a goal', expected:'reject',
    lead:'This file deliberately fails. A proof assistant is useful partly because it refuses things.',
    question:'What is Lean still asking us to prove?',
    answer:'The line after ⊢ is the remaining goal. Here it is 2 + 2 = 5. No proof tactic can establish that false equation in Lean’s usual consistent theory. Correct the claim instead.',
    source:`theorem arithmetic : 2 + 2 = 5 := by
  rfl
`,
    solution:`theorem arithmetic : 2 + 2 = 4 := by
  rfl
`,
    tryIt:'Run the original and inspect the error. Change 5 to 4 and run again. You can also remove rfl to see an unfinished goal.',
    takeaway:'An error is feedback, not a negative theorem. sorry is a placeholder, not a proof; this tutorial will flag it even if Lean allows the file.',
  },
  {
    id:'every', title:'Which number?', topic:'All inputs',
    lead:'Let us stop choosing a particular number.',
    question:'Where did we say which n to use?',
    answer:'We did not. The theorem takes an arbitrary n. Its proof works without knowing that number, so it covers every natural number.',
    source:`def twice (n : Nat) : Nat := n + n

theorem twice_unfolds (n : Nat) : twice n = n + n := by
  rfl

#check twice_unfolds
#check twice_unfolds 123
`,
    tryIt:'Change twice to n + 1 without changing the claim. What breaks? Then change the claim to match the new function.',
    takeaway:'A theorem with an argument is reusable. This proof unfolds a definition; it does not test a sample of inputs.',
  },
  {
    id:'given', title:'Use what you have', topic:'exact',
    lead:'Sometimes the proof is already among the inputs.',
    question:'If h is a proof of P, what can we return when asked for a proof of P?',
    answer:'h. In tactic mode, exact h says that this term has precisely the type of the current goal. P is an arbitrary proposition, not a Boolean variable.',
    source:`theorem keep (P : Prop) (h : P) : P := by
  exact h

#check keep
`,
    tryIt:'Replace exact h with exact P. Read the type mismatch. P is the proposition; h is the evidence for it.',
    takeaway:'Read the context above ⊢ as the things you may use. A hypothesis h : P is a local assumption, not a fact discovered about the world.',
  },
  {
    id:'arrows', title:'A proof can be a function', topic:'intro · apply',
    lead:'An implication gives us a familiar shape: an input and an output.',
    question:'What would a proof of P → Q do with a proof of P?',
    answer:'It would produce a proof of Q. intro hp accepts the input. apply step turns the goal Q into the input P that step needs. exact hp supplies it.',
    source:`theorem use_step (P Q : Prop) (step : P → Q) : P → Q := by
  intro hp
  apply step
  exact hp
`,
    tryIt:'Replace the last two lines by exact step hp. Then remove exact hp in the original version to inspect the intermediate goal.',
    takeaway:'Tactics help construct a proof term. apply works backwards from the goal; function application builds the same proof forwards.',
  },
  {
    id:'pairs', title:'Two things at once', topic:'constructor',
    lead:'Suppose the result must carry two guarantees.',
    question:'How much evidence does P ∧ Q require?',
    answer:'A proof of P and a proof of Q. constructor splits that task into two goals. The dots keep the two little proofs separate. hpq.1 and hpq.2 retrieve the components.',
    source:`theorem pair_up (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

theorem take_first (P Q : Prop) (hpq : P ∧ Q) : P := by
  exact hpq.1
`,
    tryIt:'Write take_second by changing the result type and the projection. Or replace the first proof with exact ⟨hp, hq⟩.',
    takeaway:'A conjunction is a logical pair. This is the shape we need when a program promises several properties at once.',
  },
  {
    id:'cases', title:'Only two possibilities', topic:'cases',
    lead:'A Boolean really does have a small, complete set of possibilities.',
    question:'Is checking both Boolean constructors the same as testing two arbitrary inputs?',
    answer:'No: false and true exhaust the type. cases splits the proof into those exhaustive alternatives. In each branch the expression reduces, so rfl finishes.',
    source:`def toggle (b : Bool) : Bool :=
  match b with
  | false => true
  | true => false

theorem toggle_twice (b : Bool) : toggle (toggle b) = b := by
  cases b with
  | false => rfl
  | true => rfl
`,
    tryIt:'Change toggle so that it always returns true. Which branch of the proof fails?',
    takeaway:'Bool is data a program can inspect. The equation toggle (toggle b) = b is a proposition about that data.',
  },
  {
    id:'induction', title:'And one more', topic:'Induction',
    lead:'Natural numbers are also built from constructors: zero, and the successor of another number. There are infinitely many numbers, but only these two ways to build one.',
    question:'In the successor case, what extra help could a recursive proof use?',
    answer:'A proof for the smaller number. Lean calls it the induction hypothesis, ih here. rw [ih] rewrites with that equality. The induction principle justifies using the smaller case; we have not assumed the whole theorem.',
    source:`def count : Nat → Nat
  | 0 => 0
  | n + 1 => count n + 1

theorem count_is_input (n : Nat) : count n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count n + 1 = n + 1
    rw [ih]
`,
    tryIt:'Remove rw [ih] and run. Look for ih in the context and the equality after ⊢. Restore it, then change the base case of count to 1.',
    takeaway:'change exposes a definitionally equal form of the goal. rw uses a proved equality. Recursion builds values; induction builds proofs following the same structure.',
  },
  {
    id:'contract', title:'A promise about a program', topic:'Contracts',
    lead:'Let a program accept a request only when two Boolean checks succeed.',
    question:'If accept returns true, can we recover both checks as true?',
    answer:'Yes. This theorem describes the actual function accept. simp unfolds that small definition and simplifies the Boolean conjunction equation into two propositions. It does not establish that the checks report reality accurately.',
    source:`def accept (fresh permitted : Bool) : Bool := fresh && permitted

theorem accept_contract (fresh permitted : Bool)
    (h : accept fresh permitted = true) :
    fresh = true ∧ permitted = true := by
  simpa [accept] using h
`,
    tryIt:'Change && to || while keeping the theorem. The contract should fail: one successful check no longer guarantees both.',
    takeaway:'simpa simplifies the goal and an existing proof, then checks that they match. A contract is a proposition linking a program’s inputs and output.',
  },
  {
    id:'composition', title:'A promise meets a promise', topic:'Composition',
    lead:'The first function produces something the second function knows how to use.',
    question:'If f takes P to Q, and g takes Q to R, what can their composition promise?',
    answer:'It takes P to R. The intermediate guarantee Q is the connection. α, β and γ stand for any types: text, numbers, parsed documents, checked results. We do not need a theorem for every possible pair of functions.',
    source:`theorem compose_contracts
    {α β γ : Type} (f : α → β) (g : β → γ)
    (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    (hf : ∀ x, P x → Q (f x))
    (hg : ∀ y, Q y → R (g y))
    (x : α) (hx : P x) : R (g (f x)) := by
  apply hg
  apply hf
  exact hx
`,
    tryIt:'Replace the three tactics by exact hg (f x) (hf x hx). Both construct the same chain of evidence.',
    takeaway:'This small theorem explains the idea behind a contracted pipeline. Production pipelines also need to model errors, effects and explicit assumptions.',
  },
  {
    id:'boundary', title:'Who promised?', topic:'Assumptions',
    lead:'A program can report “signature valid”. That report and the document’s authenticity are different kinds of thing.',
    question:'Which input below connects the Boolean report to the authenticity claim?',
    answer:'checker_sound. This theorem requires that assumption; it does not prove it. The other assumption, accepted, says what this particular run reported. #print axioms lists global axiom dependencies, not hypotheses passed as parameters: the full theorem type matters too.',
    source:`theorem trust_boundary
    (check : String → Bool) (Authentic : String → Prop)
    (checker_sound : ∀ text, check text = true → Authentic text)
    (text : String) (accepted : check text = true) : Authentic text := by
  exact checker_sound text accepted

#check trust_boundary
#print axioms trust_boundary
`,
    tryIt:'Remove checker_sound from the parameters and try to finish the proof. What information is now missing?',
    takeaway:'An XML transform, a signature check, a graph query and a policy can all be stages. Each needs its own precise contract. In the workbench, Factoidal supplies RDF machinery; the remaining question is how its evidence reaches the Lean policy faithfully.',
  },
];
