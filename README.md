# Solveur DPLL récursif
-----------------------

### Objectif du mini projet
Le but du mini-projet est d'implémenter un solveur DPLL récursif en
OCaml. 
    Le mini projet implémentes les fonctions suivantes :
 - la fonction simplifie : int -> int list list -> int list list
 - la fonction unitaire : int list list -> int
 - la fonction pur : int list list -> int
 - la fonction solveur_dpll_rec : int list list -> int list -> int list option

### Prerequis

Il est nécessaire d'avoit ocaml installé.
Pour l'installer sur Ubuntu 20.04+ ou Debian 11 :
```console
sudo apt install ocaml ocaml-findlib ocaml-dune
```

### Compilation et exécution 

Pour compiler 
```console
make
```
Pour exécuter 
```console
./dpll "nom du fichier au format DIMACS"
```
Tester son mini-projet
----------------------

Outre les exemples de test inclus dans dpll.ml (exemple_3_12,
exemple_7_2, exemple_7_4, exemple_7_8, systeme, coloriage), vous
pouvez utiliser le Makefile en appelant

  make

pour compiler un exécutable natif et le tester sur des fichiers au
format DIMACS. Vous trouverez des exemples de fichiers à l'adresse

  https://www.irif.fr/~schmitz/teach/2022_lo5/dimacs/

Par exemple,

  ./dpll chemin/vers/sudoku-4x4.cnf

devrait répondre

SAT
-111 -112 113 -114 -121 -122 -123 124 -131 132 -133 -134 141 -142 -143 -144 -211 212 -213 -214 221 -222 -223 -224 -231 -232 -233 234 -241 -242 243 -244 311 -312 -313 -314 -321 322 -323 -324 -331 -332 333 -334 -341 -342 -343 344 -411 -412 -413 414 -421 -422 423 -424 431 -432 -433 -434 -441 442 -443 -444 0

Si vous faites des affichages pour vos propres tests, il faudra penser
à commenter ces tests pour que votre programme réponde exactement
comme indiqué juste ci-dessus. 


