This is a draft of a complete interaction net reducer, i.e., one that allows for
arbitrary nodes, not just interaction combinator nodes. I now realize this is
necessary if we want to be competitive with modern functional runtimes in
performance. We can't afford the extra cost of λ-encoding everything. Compiling
pattern-matching functions to interaction net nodes directly will be at least an
order of magnitude more efficient in practice. This runtime is, right now, 100x
slower than JS in a very primitive test. It is a good start for a JS
"interpreter". It performs about 6m rewrites per second. 30m should be
achievable by compiling to machine code (wasm, c, llvm). The remaining 20x could
come from several micro optimizations, parallelism. Or not. But I have faith.
Interaction net reduction is not heavy. The rules are lightweight, the system is
memory efficient. It just requires some work.
