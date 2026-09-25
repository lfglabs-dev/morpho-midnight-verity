# Morpho Midnight × Verity

Proves the Certora rule
[`updatePositionViewProperties`](https://github.com/morpho-org/midnight/blob/96d31343e993329e7a593dde46516a2c0cbcd142/certora/specs/UpdatePositionView.spec)
on `Midnight.updatePositionView`, imported directly from the Solidity of
[midnight@96d31343](https://github.com/morpho-org/midnight/tree/96d31343e993329e7a593dde46516a2c0cbcd142).

- [Import.lean](Midnight/Import.lean): the Solidity import
- [Spec.lean](Midnight/Spec.lean): the rule `updatePositionViewProperties` as a definition, in the CVL vocabulary, without the CVL ghosts (not needed for a single call)
- [Proof.lean](Midnight/Proof.lean): the theorem that the rule holds (supporting lemmas in [Lemmas/](Midnight/Lemmas))
- [check/](check/README.md): what is trusted and how the import is checked

```sh
git submodule update --init --recursive
./check/check.sh
```
