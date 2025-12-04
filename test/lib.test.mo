import RadixSort "../src";
import Nat32 "mo:core/Nat32";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";
import Random "mo:core/Random";

func testRadixSort(n : Nat, mod : Nat64, sort : ([var (Nat32, Nat)], Nat32) -> ()) {
  let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

  let a = VarArray.tabulate<(Nat32, Nat)>(n, func(i) = (Nat32.fromNat64(rng.nat64Range(0, mod)), i));
  var max : Nat32 = 0;
  for (x in a.vals()) max := Nat32.max(max, x.0);
  let b = VarArray.clone(a);

  sort(a, max);
  VarArray.sortInPlace(b, func(x, y) = Nat32.compare(x.0, y.0));

  for (i in Nat.range(0, n)) {
    if (a[i] != b[i]) {
      Runtime.trap("n = " # debug_show n # " mod = " # debug_show mod # " mismatch in index = " # debug_show i);
    };
  };
};

let ns = [
  1,
  2,
  3,
  4,
  8,
  10,
  100,
  1000,
  10_000,
];

let mods : [Nat64] = [
  16,
  100,
  2 ** 32,
];

for (n in ns.vals()) {
  for (mod in mods.vals()) {
    testRadixSort(n, mod, func (a, max) = RadixSort.bucketSort(a, func(x, y) = x, ?max));
    testRadixSort(n, mod, func (a, max) = RadixSort.radixSort(a, func(x, y) = x, ?max));
  };
};
