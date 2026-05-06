var e=`/* Theory that demonstrates how references work when there are implicit subtheories */\r
{\r
  signature {\r
    sort DemoSortD;\r
    sort DemoSortE;\r
    sort DemoSortF;\r
    sort DemoSortG;\r
    sort DemoSortH;\r
  },\r
  axioms {\r
    assertions {\r
      DemoSortD = subB.subA.DemoSortA; // Nested subtheories\r
      DemoSortE = subC.subA.DemoSortA; // Nested subtheories\r
      DemoSortG = DemoSortA; // This works too\r
    }\r
  },\r
  subtheories {\r
    implicit {\r
      subB: {\r
        signature {\r
          sort DemoSortB;\r
          sort DemoSortB2; \r
        },\r
        axioms {\r
          assertions {\r
            DemoSortB = subA.DemoSortA; // Asserts the identity between two sorts\r
          }\r
        },\r
        subtheories {\r
          implicit { \r
            subA: {\r
            signature {\r
              sort DemoSortA; // Coincides with subC.subA.DemoSortA\r
\r
              a : DemoSortA; // Coincides with subC.subA.a\r
              f : DemoSortA → DemoSortA; // Coincides with subC.subA.f\r
            },\r
            axioms {\r
              assertions {\r
                f(a) = a;\r
              }\r
            }\r
          }\r
          }\r
        }\r
      },\r
      subC: {\r
        signature {\r
          sort DemoSortB; // NOTE: This definition clashes with the one in subtheoryB; Not an error\r
        },\r
        axioms {\r
          \r
        },\r
        subtheories {\r
          implicit {\r
            subA: {\r
            signature {\r
              sort DemoSortA; // Coincides with subB.subA.DemoSortA\r
\r
              a : DemoSortA; // Coincides with subB.subA.a\r
              f : DemoSortA → DemoSortA; // Coincides with subB.subA.f\r
            },\r
            axioms {\r
              assertions {\r
                f(a) = a;\r
              }\r
            }\r
          }\r
          }\r
        }\r
      } \r
    }\r
  }\r
}`;export{e as default};