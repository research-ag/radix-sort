import Nat32 "mo:core/Nat32";
import Runtime "mo:core/Runtime";
import Order "mo:core/Order";
import Prim "mo:⛔";

module {
  let nat = Prim.nat32ToNat;

  // sort from buffer to dest array at the given offset
  public func insertionSortSmallMove<T>(buffer : [var T], dest : [var T], compare : (T, T) -> Order.Order, newFrom : Nat32, len : Nat32, offset : Nat32) {
    debug assert len > 0;
    switch (len) {
      case (1) {
        dest[nat(offset)] := buffer[nat(newFrom)];
      };
      case (2) {
        let t0 = buffer[nat(newFrom)];
        let t1 = buffer[nat(newFrom +% 1)];
        if (compare(t1, t0) == #less) {
          dest[nat(offset)] := t1;
          dest[nat(offset +% 1)] := t0;
        } else {
          dest[nat(offset)] := t0;
          dest[nat(offset +% 1)] := t1;
        };
      };
      case (3) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        let t2 = buffer[nat(newFrom +% 2)];

        if (compare(t1, t0) == #less) {
          let v = t1;
          t1 := t0;
          t0 := v;
        };

        if (compare(t2, t1) == #less) {
          if (compare(t2, t0) == #less) {
            dest[nat(offset)] := t2;
            dest[nat(offset +% 1)] := t0;
            dest[nat(offset +% 2)] := t1;
          } else {
            dest[nat(offset)] := t0;
            dest[nat(offset +% 1)] := t2;
            dest[nat(offset +% 2)] := t1;
          };
        } else {
          dest[nat(offset)] := t0;
          dest[nat(offset +% 1)] := t1;
          dest[nat(offset +% 2)] := t2;
        };
      };
      case (4) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];

        if (compare(t1, t0) == #less) {
          let v = t1;
          t1 := t0;
          t0 := v;
        };

        var tv = t2;
        if (compare(tv, t1) == #less) {
          t2 := t1;
          if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
            t1 := tv;
          };
        };

        if (compare(t3, t2) == #less) {
          tv := t3;
          t3 := t2;
          if (compare(tv, t1) == #less) {
            t2 := t1;
            if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
              t1 := tv;
            };
          } else { t2 := tv };
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
      };
      case (5) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];

        if (compare(t1, t0) == #less) {
          let v = t1;
          t1 := t0;
          t0 := v;
        };
        var tv = t2;
        if (compare(tv, t1) == #less) {
          t2 := t1;
          if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
            t1 := tv;
          };
        };
        tv := t3;
        if (compare(tv, t2) == #less) {
          t3 := t2;
          if (compare(tv, t1) == #less) {
            t2 := t1;
            if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
              t1 := tv;
            };
          } else { t2 := tv };
        };
        tv := t4;
        if (compare(tv, t3) == #less) {
          t4 := t3;
          if (compare(tv, t2) == #less) {
            t3 := t2;
            if (compare(tv, t1) == #less) {
              t2 := t1;
              if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                t1 := tv;
              };
            } else { t2 := tv };
          } else { t3 := tv };
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
      };
      case (6) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];
        var t5 = buffer[nat(newFrom +% 5)];

        if (compare(t1, t0) == #less) {
          let v = t1;
          t1 := t0;
          t0 := v;
        };
        var tv = t2;
        if (compare(tv, t1) == #less) {
          t2 := t1;
          if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
            t1 := tv;
          };
        };
        tv := t3;
        if (compare(tv, t2) == #less) {
          t3 := t2;
          if (compare(tv, t1) == #less) {
            t2 := t1;
            if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
              t1 := tv;
            };
          } else { t2 := tv };
        };
        tv := t4;
        if (compare(tv, t3) == #less) {
          t4 := t3;
          if (compare(tv, t2) == #less) {
            t3 := t2;
            if (compare(tv, t1) == #less) {
              t2 := t1;
              if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                t1 := tv;
              };
            } else { t2 := tv };
          } else { t3 := tv };
        };
        tv := t5;
        if (compare(tv, t4) == #less) {
          t5 := t4;
          if (compare(tv, t3) == #less) {
            t4 := t3;
            if (compare(tv, t2) == #less) {
              t3 := t2;
              if (compare(tv, t1) == #less) {
                t2 := t1;
                if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                  t1 := tv;
                };
              } else { t2 := tv };
            } else { t3 := tv };
          } else { t4 := tv };
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
        dest[nat(offset +% 5)] := t5;
      };
      case (7) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];
        var t5 = buffer[nat(newFrom +% 5)];
        var t6 = buffer[nat(newFrom +% 6)];

        if (compare(t1, t0) == #less) {
          let v = t1;
          t1 := t0;
          t0 := v;
        };
        var tv = t2;
        if (compare(tv, t1) == #less) {
          t2 := t1;
          if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
            t1 := tv;
          };
        };
        tv := t3;
        if (compare(tv, t2) == #less) {
          t3 := t2;
          if (compare(tv, t1) == #less) {
            t2 := t1;
            if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
              t1 := tv;
            };
          } else { t2 := tv };
        };
        tv := t4;
        if (compare(tv, t3) == #less) {
          t4 := t3;
          if (compare(tv, t2) == #less) {
            t3 := t2;
            if (compare(tv, t1) == #less) {
              t2 := t1;
              if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                t1 := tv;
              };
            } else { t2 := tv };
          } else { t3 := tv };
        };
        tv := t5;
        if (compare(tv, t4) == #less) {
          t5 := t4;
          if (compare(tv, t3) == #less) {
            t4 := t3;
            if (compare(tv, t2) == #less) {
              t3 := t2;
              if (compare(tv, t1) == #less) {
                t2 := t1;
                if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                  t1 := tv;
                };
              } else { t2 := tv };
            } else { t3 := tv };
          } else { t4 := tv };
        };
        tv := t6;
        if (compare(tv, t5) == #less) {
          t6 := t5;
          if (compare(tv, t4) == #less) {
            t5 := t4;
            if (compare(tv, t3) == #less) {
              t4 := t3;
              if (compare(tv, t2) == #less) {
                t3 := t2;
                if (compare(tv, t1) == #less) {
                  t2 := t1;
                  if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                    t1 := tv;
                  };
                } else { t2 := tv };
              } else { t3 := tv };
            } else { t4 := tv };
          } else { t5 := tv };
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
        dest[nat(offset +% 5)] := t5;
        dest[nat(offset +% 6)] := t6;
      };
      case (8) {
        var t0 = buffer[nat(newFrom)];
        var t1 = buffer[nat(newFrom +% 1)];
        var t2 = buffer[nat(newFrom +% 2)];
        var t3 = buffer[nat(newFrom +% 3)];
        var t4 = buffer[nat(newFrom +% 4)];
        var t5 = buffer[nat(newFrom +% 5)];
        var t6 = buffer[nat(newFrom +% 6)];
        var t7 = buffer[nat(newFrom +% 7)];

        if (compare(t1, t0) == #less) {
          let v = t1;
          t1 := t0;
          t0 := v;
        };
        var tv = t2;
        if (compare(tv, t1) == #less) {
          t2 := t1;
          if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
            t1 := tv;
          };
        };
        tv := t3;
        if (compare(tv, t2) == #less) {
          t3 := t2;
          if (compare(tv, t1) == #less) {
            t2 := t1;
            if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
              t1 := tv;
            };
          } else { t2 := tv };
        };
        tv := t4;
        if (compare(tv, t3) == #less) {
          t4 := t3;
          if (compare(tv, t2) == #less) {
            t3 := t2;
            if (compare(tv, t1) == #less) {
              t2 := t1;
              if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                t1 := tv;
              };
            } else { t2 := tv };
          } else { t3 := tv };
        };
        tv := t5;
        if (compare(tv, t4) == #less) {
          t5 := t4;
          if (compare(tv, t3) == #less) {
            t4 := t3;
            if (compare(tv, t2) == #less) {
              t3 := t2;
              if (compare(tv, t1) == #less) {
                t2 := t1;
                if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                  t1 := tv;
                };
              } else { t2 := tv };
            } else { t3 := tv };
          } else { t4 := tv };
        };
        tv := t6;
        if (compare(tv, t5) == #less) {
          t6 := t5;
          if (compare(tv, t4) == #less) {
            t5 := t4;
            if (compare(tv, t3) == #less) {
              t4 := t3;
              if (compare(tv, t2) == #less) {
                t3 := t2;
                if (compare(tv, t1) == #less) {
                  t2 := t1;
                  if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                    t1 := tv;
                  };
                } else { t2 := tv };
              } else { t3 := tv };
            } else { t4 := tv };
          } else { t5 := tv };
        };
        tv := t7;
        if (compare(tv, t6) == #less) {
          t7 := t6;
          if (compare(tv, t5) == #less) {
            t6 := t5;
            if (compare(tv, t4) == #less) {
              t5 := t4;
              if (compare(tv, t3) == #less) {
                t4 := t3;
                if (compare(tv, t2) == #less) {
                  t3 := t2;
                  if (compare(tv, t1) == #less) {
                    t2 := t1;
                    if (compare(tv, t0) == #less) { t1 := t0; t0 := tv } else {
                      t1 := tv;
                    };
                  } else { t2 := tv };
                } else { t3 := tv };
              } else { t4 := tv };
            } else { t5 := tv };
          } else { t6 := tv };
        };

        dest[nat(offset)] := t0;
        dest[nat(offset +% 1)] := t1;
        dest[nat(offset +% 2)] := t2;
        dest[nat(offset +% 3)] := t3;
        dest[nat(offset +% 4)] := t4;
        dest[nat(offset +% 5)] := t5;
        dest[nat(offset +% 6)] := t6;
        dest[nat(offset +% 7)] := t7;
      };
      case (_) Runtime.trap("insertionSortSmall for len > 8 is not implemented.");
    };
  };
};
