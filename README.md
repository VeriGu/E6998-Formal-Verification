# E6998-Formal-Verification

## Coq installation

We use `opam` to install Coq and other dependencies. To install `opam`:
  - Ubuntu:
  ```
  sudo apt install opam
  ```
  - Mac OS X:
  ```
  brew install opam
  ```

Then, initialize `opam` with the specific version `4.03.0`:
  ```
  opam init --compiler 4.03.0
  ```
If your `opam` has a different version, switch to `4.03.0`:
  ```
  opam switch create 4.03.0
  ```
Then, use `opam` to install `coq 8.6` and `menhir 20170101`
```
opam install coq.8.6 menhir.20170101
```
Make sure `coqc` is in your system `PATH`, or add it manually:
```
export PATH="path/to/.opam/4.03.0/bin":$PATH
```
`.opam/` is usually in your home folder.

## Proof-General installation

Proof-General is a powerful plugin of Emacs that helps developing Coq. Just make sure you have Emacs.
```
sudo apt install emacs   (with a version at least emacs25)
```

I recommend installing Emacs together with `spacemacs` (https://github.com/syl20bnr/spacemacs).
```
git clone https://github.com/syl20bnr/spacemacs ~/.emacs.d
```

If installing `spacemacs`, it will take some time for initialization during the first time you open Emacs. After `spacemacs` initialized, you can open  `~/.spacemacs` and edit the `dotspacemacs-additional-packages` item with:
```
dotspacemacs-additional-packages '(proof-general company-coq)
```
 
Then the next time you start Emacs, it will install proof-general automatically. About company-coq, you can find more information from https://github.com/cpitclaudel/company-coq. You might want to add the following line into ~/.emacs.d/init.el so that it can enter coq-mode automatically when you edit `*.v` files.
```
(add-hook 'coq-mode-hook #'company-coq-mode)
```
Here's a tutorial on Youtube for the usage of proof-general. https://www.youtube.com/watch?v=l6zqLJQCnzo

## Compile Lectures and Assignments

Simply run `make` under the root folder of this repo. If it does not work, try:
```
coq_makefile -f _CoqProject -o Makefile
```
Then `make`.

## Compile CertiKOS

To compile CertiKOS, `cd certikos/`. Then,
- for Linux users,
    ```
    ./configure x86_64-linux
    ```
- for Mac users,
    ```
    ./configure x86_64-macosx
    ```
And compile,
```
make -j6
```
