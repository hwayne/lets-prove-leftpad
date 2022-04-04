# B
## About B
[B method](https://www.atelierb.eu/en/presentation-of-the-b-method/) was created in the 1980s by Jean-Raymond Abrial. It is a method for developing formally verified software. The method suggests starting with an abstract specification and incrementally refining it until the low-level deterministic model of the system is achieved, which in turn can be used to generate code. Software designed this way is called correct by construction.

The most famous application: driverless Paris Métro line 14. 115 000 lines of B models were written and fully proven, 86 000 lines of Ada code were automatically generated. Citation from [Formal Methods in Safety-Critical Railway Systems](https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/8/1/fm_sc_rs_v2.pdf):

> No bugs were detected after the proofs, neither at the functional validation, at the integration validation, at on-site test, nor since the metro lines operate (October 1998). The safety-critical software is still in version 1.0 in year 2007, without any bug detected so far.

[B language](https://en.wikipedia.org/wiki/B-Method) is based on set theory and first order logic. It is supported by [Atelier B](https://www.atelierb.eu/en/): an industrial tool focused on developing safety-critical systems. There is also [ProB](https://prob.hhu.de/w/index.php?title=The_ProB_Animator_and_Model_Checker): animator, constraint solver and model checker for B, which also supports Event-B, TLA+, Alloy by translating them into B.

Learning materials:
* The B-Book: Assigning Programs to Meanings by J. R. Abrial
* Manuals available inside Atelier B (Help -> Manuals)
* [Unfinished online course](https://mooc.imd.ufrn.br/course/the-b-method)
* Documentation and examples from [the ProB site](https://prob.hhu.de/w/index.php?title=The_ProB_Animator_and_Model_Checker)

## About the Proof
Usually B models define a state machine, which consists of state variables, invariants and operations. Operations change values of the variables, and thus can violate invariants, so naturally one of the goals of the verification process is to prove that invariants hold in all possible states.

The presented model does not contain states and invariants. Instead, there is a single operation titled *leftpad*, which takes 3 arguments and returns an output. The model consists of 2 files: [Leftpad.mch](Leftpad.mch) and [Leftpad_i.imp](Leftpad_i.imp). In the first file the *leftpad* operation defined declaratively: instead of stating how operation should be implemented, we state what it should do. This directly corresponds to the properties that need to be proven about leftpad, which are defined in the [top-level readme](../README.md).

The second file contains the imperative implementation of the leftpad. This implementation is not independent from the first declarative specification: in fact, this is its refinement. Refinement is the core concept in the B method: if operation B refines operation A, then it can only behave in a way that corresponds to the behavior of A (actually, refinement is defined between 2 models, their states and operations).

This correspondence must be explicitly proved in the B method — and it is exactly what we need to prove to demonstrate the correctness of the leftpad implementation.

For each case that requires proof (invariant preservation, well-definedness of expressions, correctness of the refinement, etc.), Atelier B automatically generates a proof obligation. All proof obligations must be proven in order to verify the model. This can be done fully automatically by using Atelier B provers, or using interactive proving interface.

For leftpad, Atelier B generates 46 proof obligations, of which 7 can’t be proved automatically. To prove them, some typical actions were performed: splitting the proof into cases, adding new hypothesis, instantiation of a universally quantified hypothesis, equality rewrites. This was fairly simple and straitfarward.

Some notes about the proof:
* All the properties, loop invariants, variants, and the code itself were directly inspired by the [Dafny proof](../dafny/readme.md) (there is almost 1-to-1 correspondence).
* Sequence indexing in B is 1-based, so all the properties was changed to accommodate this.
* Atelier B parser doesn’t work with single-letter variables, so instead of `i` there is `ii`, instead of `n` — `nn`, and so on.
* The proof was conducted using Atelier B 4.7.1 Community Edition. ProB 1.11.1 was used to animate and validate the models.
* `*.pup` files contain interactive proofs for 7 proof obligations. They are not human readable.

## About me
My name is Ilya Shchepetkov. This is my first B model, but I’ve been using Event-B and other formal methods for work for the last 9 years. Here is my [Instagram](https://www.instagram.com/17451k/), because why not.
