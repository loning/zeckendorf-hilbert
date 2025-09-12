# Translation Guidelines for Hilbert-Complete Theory

## Translation Protocol

### File Naming Convention
- Original file: `filename.md`
- English translation: `filename_en.md`
- Maintain directory structure exactly

### Core Instructions from CLAUDE.md

#### Mathematical Standards
- **Fibonacci Sequence Definition**: F₁=1, F₂=2, F₃=3, F₄=5, F₅=8, F₆=13, F₇=21, F₈=34, F₉=55, F₁₀=89, F₁₁=144, F₁₂=233, F₁₃=377, F₁₄=610, F₁₅=987, F₁₆=1597...
- **Formula Format**: Use LaTeX with $ and $$ notation
- **$$ should be on separate lines**
- **No time constraints** - maintain highest quality
- **No modification logs needed** - direct implementation
- **English version files end with _en.md**

#### Content Standards
- **No simplification** - preserve full mathematical rigor
- **Direct translation** - do not improvise or add content
- **Preserve all mathematical notation exactly**
- **Maintain theorem numbering and references**
- **Keep all boxed formulas and key results**

#### Quality Assurance
- **Mathematical accuracy is paramount**
- **Logical consistency must be preserved**
- **Flag any inconsistencies immediately**
- **Report both in chat and create error logs**
- **Distinguish between gaps/overstating vs. actual errors**
- **Uncertainty logging required**: Maintain detailed log of any content translator is not 100% certain about
- **Critical review**: Question notational consistency and logical flow throughout

### Translation Focus Areas

#### Critical Elements to Preserve
1. **Recursive Mother Space**: $\mathcal{H}^{(R)} = \overline{\bigcup_{n=0}^\infty \mathcal{H}_n^{(R)}}$
2. **Relativistic Indices**: $\eta^{(R)}(l; m)$ parameterization
3. **Tag Sequences**: $f_n = \sum_{k=0}^n a_k e_k$
4. **Self-referential equations**: ψ = ψ(ψ) concepts
5. **Five-fold equivalence**: Entropy ↔ Asymmetry ↔ Time ↔ Information ↔ Observer

#### Mathematical Rigor Checkpoints
- **Definition precedence**: Ensure definitions come before usage
- **Proof completeness**: Verify all claimed proofs are complete
- **Reference accuracy**: Check all theorem and section references
- **Notation consistency**: Maintain consistent mathematical notation
- **Logical flow**: Ensure conclusions follow from premises

### Error Reporting Protocol

#### When to Flag Issues
1. **Mathematical errors**: Incorrect formulas, invalid proofs
2. **Logical inconsistencies**: Contradictory statements
3. **Undefined terms**: Usage before definition
4. **Circular reasoning**: Self-referential logic without proper foundation
5. **Incomplete proofs**: Claims without adequate mathematical support

#### How to Report
1. **Immediate chat notification** with specific location
2. **Create detailed error log** with exact issues
3. **Distinguish between**:
   - Actual mathematical errors (must fix)
   - Theoretical gaps (acknowledge but may be acceptable)
   - Overstated claims (clarify but may be visionary)

### Quality Standards
- **No reduction in mathematical sophistication**
- **Preserve all technical terminology**
- **Maintain academic tone and rigor**
- **Keep all philosophical depth**
- **Preserve the visionary aspects while noting their status**

---

**Remember**: This is serious mathematical research that pushes boundaries. The goal is faithful translation that preserves both the mathematical rigor and the ambitious theoretical vision, while being honest about any logical gaps or overstated claims.
