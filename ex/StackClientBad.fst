module StackClientBad

  let main =
    let s0 = Stack.empty in
    let s1 = Stack.push 3 s0 in
    2 :: s1
