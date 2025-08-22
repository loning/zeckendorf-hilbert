#!/bin/bash
# Zero-Admit Collapse-Aware Coq Environment Setup
# Installs all libraries needed for complete Qed proofs

echo "🚀 Installing Zero-Admit Collapse-Aware Coq Libraries..."

# Core MathComp ecosystem (constructive)
echo "📦 Installing MathComp core..."
opam install coq-mathcomp-ssreflect -y
opam install coq-mathcomp-algebra -y  
opam install coq-mathcomp-algebra-tactics -y

# Advanced analysis (constructive real numbers)
echo "📐 Installing constructive analysis..."
opam install coq-mathcomp-analysis -y

# Interval arithmetic for inequalities
echo "🔢 Installing interval arithmetic..."
opam install coq-interval -y

# Extended libraries for list operations
echo "📋 Installing extended libraries..."
opam install coq-ext-lib -y

# Equations for well-founded recursion
echo "🔄 Installing recursion support..."
opam install coq-equations -y

# BigNum for large integer computations
echo "🔢 Installing big numbers..."
opam install coq-bignums -y

echo "✅ Zero-Admit environment ready!"
echo "🎯 All libraries support constructive proofs with complete Qed"
echo "🔥 Ready for collapse-aware formal verification ∎"