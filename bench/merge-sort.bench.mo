import Bench "mo:bench";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import VarArray "mo:core/VarArray";
import Option "mo:core/Option";
import Sort "../src";

module {
  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Sort small");
    bench.description("Compare insertion sort and batcher sort");

    let rows = [
      "merge",
      "bucket",
    ];
    let cols = [
      "10",
      "20",
      "40",
      "80",
      "160",
      "320",
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

    bench.runner(
      func(row, col) {
        let n = Option.unwrap(Nat.fromText(col));
        let a : [var Nat32] = VarArray.tabulate<Nat32>(n, func(i) = Nat64.toNat32(rng.nat64() % (2 ** 32)));
        if (row == "merge") Sort.mergeSort(a, func i = i) else Sort.bucketSort(a, func i = i, null);
      }
    );

    bench;
  };
};
