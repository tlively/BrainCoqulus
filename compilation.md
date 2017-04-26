# Compilation Strategy
A stack machine will be used to implement a lambda calculus with natural numbers and explicit environment. Each unique lambda subterm in the input program will be assigned an index, and the indices will be used to locate the Brainfuck code implementing the corresponding term in the Brainfuck function table. This way, functions can be identified by simple numbers on the stack. Closures are represented as tuples combining their base function and instances of the function's free variables.

## Input and Output Languages
The stack machine code is compiled from the following modified call by value lambda calculus with natural numbers.

```
e ::= n
    | x_i (* indexed argument *)
    | lambda. e
    | apply e1 e2
    | out e
```

The high level stack machine language is
```
e ::= push v  (* push constant v onto the stack *)
    | del k   (* remove the head from the stack *)
    | get k   (* copy the element at depth k to the head of the stack *)
    | pack k  (* pack the top k elements of the stack into a tuple *)
    | unpack  (* unpack the top element of the stack *)
    | call
    | out
```
This high level stack machine language is not directly implementable in Brainfuck, so it will be lowered to a similar lower level stack machine language. The details of this lowering will be explained as necessary.


## Stack Layout
Logically, the stack is just a list of items, and items are just natural numbers or tuples of items. However, this logical stack ultimately needs to be implemented in Brainfuck as a physical stack.

The physical stack is made up variable-sized *items* separated by zero-valued cells to aid navigation. However, it is necessary to be able to distinguish zero-valued items from item separators, so we cluster physical cells into pairs in which the first cell is a tag cell and the second cell is a data cell. Each of these pairs of physical cells is called a *logical cell*. Each stack item is made of one or more contiguous logical cells.

```
Physical cells: [tag][data] [tag][data] [tag][data] ...
Logical cells:  [ cell 0  ] [ cell 1  ] [ cell 2  ] ...
```

A nonzero tag means the logical cell contains the value of the data cell and a tag value of 0 means the logical cell contains no value and is a stack item separator. Tuples are implemented as contiguous sequences of logical cells with tag equal to *n+1* and internal separator tags equal to *n*. For example the physical stack corresponding to the logical stack `a, b, (c, d, (e, f))` would look like

```
---------------------------------------------------------------------------------------
1 | a | 0 | _ | 1 | b | 0 | _ | 2 | c | 1 | _ | 2 | d | 1 | _ | 3 | e | 2 | _ | 3 | f |
---------------------------------------------------------------------------------------
```

Taking the predecessor of all the tags within the last item on the stack (the tuple) gives

```
---------------------------------------------------------------------------------------
1 | a | 0 | _ | 1 | b | 0 | _ | 1 | c | 0 | _ | 1 | d | 0 | _ | 2 | e | 1 | _ | 2 | f |
---------------------------------------------------------------------------------------
```

Which is equivalent to the stack `a, b, c, d, (e, f)`. In other words, the operation that expands a tuple onto the stack is simply decrementing each tag inside it. Similarly, to create a tuple of the top *k* elements of the stack, one simply has to increment the tags within the last *k* items and the *k-1* separator cells between them. Since Brainfuck navigates the stack most efficiently by looking for delimiting zeroes, this implementation of tuples will be relatively straightforward and efficient. Tuples are used to group function IDs and free variable values into complete closures. In the future they may also be used as an optimized implementation of lists.

The Brainfuck implementation details are omitted here because the implementation will be built with a richer tape language than Brainfuck, but the stack language specification semantics are presented below.

## Stack Machine Specification
The stack pointer always points one physical cell past the last item on the stack before and after executing an operation. Data beyond the stack is not assumed to be zeroed out, which improves performance because it allows out old data to only be cleared when necessary.

### Push
This is the simplest type of expression. It just pushes a natural number *n* onto the stack,
```
{[<stack>]} push n; {[<stack>,n]}
```

### Del k
Removes the *k*th element of the stack.
```
{[<stack>,xk,x(k-1),...,x1]} del k; {[<stack>,x(k-1),...,x1]}
```

### Get k
Copies the *k*th element of the stack to the head.
```
{[<stack>,xk,...,x1]} get k; {[<stack>,xk,...,x1,xk]}
```

### Pack k
Pack the top *k* elements into a tuple.
```
{[<stack>,xk,...,x1]} pack k; {[<stack>,(xk,...,x1)]}
```

### Unpack
If the top element of the stack is a tuple, place its subelements on the stack.
```
{[<stack>,(xk,...,x1)]} unpack; {[<stack>,xk,...,x1]}
```

### Function Call
The function's argument is laid out on the stack first, followed by the function's ID *f*. After the function completes, its result *r* is left on the stack. The function body begins only with the argument on the stack, since *f* is consumed by the runtime during the location of the funtion.
```
{[<stack>,x]} f {[<stack>,f(x)]}
{[<stack>,x,f]} call; {[<stack>,f(x)]}
```
In the highest level stack language, control returns to the call site when the called function terminates. Unfortunately these semantics are impossible to implement directly in Brainfuck, so there will be a lower level stack language in which function bodies are split around call instructions such that the call is always the last instruction in a function body. Since the call instructions occur only at the end of function bodies and occur at the end of every function body, they are removed from the language and made explicit in the semantics.
```
Higher level
f: a1; ...; an; push g; call; b1; ...; bk;

Lower level
f0: a1; ...; an; push f1; copy 1; del 2; push g; <implicit jump>
f1: b1; ...; bk; <implicit jump>;
```
*note:* If a call is ever preceded by anything other than a push (such as a get), this lowering will need to be adapted to the other patterns.

### Closure Call
The closure's argument is laid out on the stack first, followed by the closure tuple. The closure tuple contains the arguments laid out left to right from lowest to highest DeBruijn index followed by the function ID *f*. The tuple is expanded and the function ID is gone when the function body begins execution. The same transformation used to lower function calls is used to lower closure calls.
```
{[<stack>,x0,x1,...,xn]} f {[<stack>,f(x0,...,xn)]}
{[<stack>,x0,(x1,...,xn,f)]} call; {[<stack>,f(x0,...,xn)]}
```

### Output
The output expression prints the value of the head of the stack if it represents the Church encoding of a natural number.
```
{[<stack>,x]} out; {[<stack>,x]}
```
Since the Church encoding of a natural number *n* is a term that takes *f* and *x* and applies *f* to *x* *n* times, the out command is implemented as an application of the closure or function at the head of the stack to a builtin function, *add*, that simply increments the number at the head of the stack using the inc command, and 0. This makes the head of the stack equal to *n*. Finally, another builtin function, *out*, is called. *out* simply outputs the integer at the head of the stack using the lower level stack language command out without removing its argument from the stack. The lowering transformation expands the higher level out command into a series of calls, then the calls are lowered as normal.
```
Higher level
f: a1; ...; an; out; b1; ...; bk;

Higher level (expanded)
f0: a1; ...; an; push 0; push add; get 2; call; call; push out; call; del 0; b1; ...; bk;
```

## Example Transformation
Consider the following complete lambda expression with integer primitives.
```
(\x.\y.x) 5 7
```
This expression is represented by the following partially expanded AST with De Bruijn indices.
```
Out
    App
        (App (\.\.1) 5)
        7
```
The high level stack machine code implementing this computation is
```
main:
    push 7;
    push 5;
    push f0;
    call;
    call;
    out;
f0:
    push f1;
    pack 2;
f1:
    del 1;
```
Where `f0` is the function ID of `\.\.1` and `f1` is the function ID of `\.1`.

## Remaining Specification Work
The semantics above are up for debate. Things to think about: is there a way we can make function and closure calls more similar? Should the runtime be responsible for expanding the tuples as above or should user code be responsible for expanding the tuples? Should we add a flat_pack operator that combines the top *k* items into a tuple without increasing the nesting level of items that are already tuples?

Although the stack machine languages described above will be our bridge between the functional and imperative domains, we still need a higher level language that operates directly on the Brainfuck tape in which to implement this stack machine. This language will need proper control flow structures such as conditional statements and loops, which will require boolean expressions. Fortunately, however, it will not need more advanced features such as functions, since it is being used to implement functions in the stack machine. This brainfuck with control flow should be relatively easy to build on BFN, but it will be important to keep the stack abstraction in mind when implementing it to keep the proof as simple as possible.