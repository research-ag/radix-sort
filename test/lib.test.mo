import Sort "../src";
import Nat32 "mo:core/Nat32";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import Order "mo:core/Order";
import VarArray "mo:core/VarArray";

func sortInPlace<T>(array : [var T], compare : (T, T) -> Order.Order) : () {
  // Stable merge sort in a bottom-up iterative style. Same algorithm as the sort in Buffer.
  let size = array.size();
  if (size == 0) {
    return;
  };
  let scratchSpace = VarArray.repeat<T>(array[0], size);

  var currSize = 1; // current size of the subarrays being merged
  var oddIteration = false;

  // when the current size == size, the array has been merged into a single sorted array
  while (currSize < size) {
    let (fromArray, toArray) = if (oddIteration) (scratchSpace, array) else (array, scratchSpace);
    var leftStart = 0; // selects the current left subarray being merged

    while (leftStart < size) {
      let mid = if (leftStart + currSize < size) leftStart + currSize else size;
      let rightEnd = if (leftStart + 2 * currSize < size) leftStart + 2 * currSize else size;

      // merge [leftStart, mid) with [mid, rightEnd)
      var left = leftStart;
      var right = mid;
      var nextSorted = leftStart;
      while (left < mid and right < rightEnd) {
        let leftElement = fromArray[left];
        let rightElement = fromArray[right];
        toArray[nextSorted] := switch (compare(leftElement, rightElement)) {
          case (#less or #equal) {
            left += 1;
            leftElement;
          };
          case (#greater) {
            right += 1;
            rightElement;
          };
        };
        nextSorted += 1;
      };
      while (left < mid) {
        toArray[nextSorted] := fromArray[left];
        nextSorted += 1;
        left += 1;
      };
      while (right < rightEnd) {
        toArray[nextSorted] := fromArray[right];
        nextSorted += 1;
        right += 1;
      };

      leftStart += 2 * currSize;
    };

    currSize *= 2;
    oddIteration := not oddIteration;
  };
  if (oddIteration) {
    var i = 0;
    while (i < size) {
      array[i] := scratchSpace[i];
      i += 1;
    };
  };
};

func testRadixSort(n : Nat) {
  let A : Nat32 = 1664525;
  let C : Nat32 = 1013904223;

  var seed : Nat32 = 12345;

  var a = VarArray.tabulate<(Nat32, Nat)>(
    n,
    func(i) {
      seed := seed *% A +% C;
      (seed, i);
    },
  );

  let b = VarArray.clone(a);

  Sort.radixSort<(Nat32, Nat)>(a, func(x, y) = x);
  sortInPlace(b, func(x, y) = Nat32.compare(x.0, y.0));

  for (i in Nat.range(0, n)) {
    if (a[i] != b[i]) {
      Runtime.trap("Mismatch in index = " # debug_show i);
    };
  };
};

testRadixSort(4);
testRadixSort(10);
testRadixSort(100);

Sort.radixSort<Nat32>([var 5, 1, 2, 3, 4], func i = i);