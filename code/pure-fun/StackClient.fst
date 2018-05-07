module StackClient

  let main =
    let s0 = Stack.empty in
    let s1 = Stack.push 3 s0 in
    let s2 = Stack.push 4 s1 in
    Stack.top s2
