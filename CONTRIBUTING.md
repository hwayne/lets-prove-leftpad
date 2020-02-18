# Contributing Guidelines

## Adding a Leftpad

Check out the "dafny" folder for an example of what this all looks like.

One folder per leftpad, one leftpad per folder. If you're the first person uploading for your proof language, name the folder after your method. If someone else already submitted a proof, you should postpend your folder with what makes your leftpad proof special. For example, we already have "Dafny", but it's done with mutations and loop invariants, so if you write a version using pure functions and recursion, you should name it something like "Dafny (Functional)". We might reject a PR if the proof is too similar to another one in the same language.

Your code should formally prove the total specification of Leftpad. It must do this without any assumptions in the proof, and the proof must correct. Proving intermediate lemmas or ghost functions is fine, as are using already-proven primitives your language's standard library.

Along with your leftpad, you should include a `readme.md` file. It should contain:
* The name of your tool, and a link to learn more about it.
* A link to an online demo of your leftpad, if your language has one.
* A description of the language. What does it look like? How does it work? What makes it different or special?
* A description of your proof. How does it work? What interesting language properties or verification techniques does it showcase?
* Anything you want to plug, like your website or twitter or CV. You proved Leftpad! Brag a bit!

That's pretty much it!
