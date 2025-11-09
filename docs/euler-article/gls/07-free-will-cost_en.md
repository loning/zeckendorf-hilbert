# The Cost of Free Will: Directed Information and the Physics of Choice

## Humanity's Oldest Debate

Do you have free will?

For thousands of years, this question has torn apart philosophers, theologians, and scientists:

**Determinists say:** The universe is a causal chain, each event determined by previous events. Your "choices" are just results of brain neurons operating according to physical laws—freedom is an illusion.

**Free will advocates say:** Humans have real ability to choose, otherwise morality, responsibility, meaning all lose foundation. Freedom is human essence.

**Compatibilists say:** Freedom and determinism can coexist—as long as you act "according to your will," that's freedom, regardless of whether will itself is determined.

In 2024, physics gives a fourth answer:

**Free will is not a metaphysical concept, but a measurable physical quantity—it's the directed information your actions produce on the future, and this has physical lower bounds and energy costs.**

Freedom is not all-or-nothing, but **degree**—and this degree can be calculated with information theory.

---

## Act I: Definition of Freedom

What is freedom?

### Problems with Naive Definitions

**"Can do what I want"** — But where does "want" come from? If "want" is determined by brain state, is this freedom?

**"Not forced by external forces"** — But genes, education, culture are all "external forces," can you escape them?

**"Can choose otherwise"** — But under same initial conditions, physical laws give same results, where's "otherwise"?

### Information-Theoretic Definition

GLS framework gives operational definition:

**Degree of freedom = How much distinguishable influence your actions can have on the future**

Formalized:

$$
\text{Freedom} = I(M^n \to Y^n)
$$

where:
- $M^n = (M_1, M_2, \ldots, M_n)$: Your action sequence
- $Y^n = (Y_1, Y_2, \ldots, Y_n)$: Future you observe
- $I(M^n \to Y^n)$: **Directed information**

### What Is Directed Information?

Definition:

$$
I(M^n \to Y^n) = \sum_{i=1}^n I(M^i; Y_i | Y^{i-1})
$$

It measures: **Given past observations, how much new information do your actions provide about current observation.**

In plain language:
- If your actions completely don't affect future, $I = 0$ (**no freedom**)
- If your actions significantly change future, $I$ is large (**high freedom**)

**Freedom = information measure of causal influence.**

---

## Act II: Physical Lower Bounds of Freedom

Now key question: Does freedom have lower bounds?

Answer: **Yes, and profound.**

### Condition 1: Directed Information Lower Bound

To have free will, must have:

$$
I(M^n \to Y^n) > c_1 > 0
$$

**Your actions must be able to affect future, and this influence is measurable.**

If $I = 0$, means:
- Your actions are random noise (unrelated to future)
- Or your actions are completely passive (determined by outside)

**No influence = no freedom.**

### Condition 2: Empowerment Lower Bound

Define **Empowerment**:

$$
\mathcal{E}_k = \max_{p(a^k)} I(A^k; S_{k+1})
$$

It measures: **Your future $k$ steps of actions, maximum influence on state.**

To have freedom, need:

$$
\mathcal{E}_k > c_2 > 0
$$

**You must have potential choice space—can do different things.**

### Condition 3: Energy-Information Trade-off

Most profound constraint comes from thermodynamics:

$$
\langle W \rangle \geq \Delta F - k_B T \langle I \rangle
$$

This is corollary of **Jarzynski-Sagawa-Ueda equality**:

**Information $I$ you acquire can reduce need for work $W$, but has cost.**

From another angle:

$$
\langle W \rangle + k_B T \langle I \rangle \geq \Delta F
$$

**Freedom requires energy: either consume physical work $W$, or consume information processing cost $k_B T I$.**

---

## Act III: The Cost of Freedom

Freedom is not free.

### Brain's Energy Consumption

Human brain:
- Mass: ~1.4kg (2% of body weight)
- Energy consumption: ~20W (20% of total metabolism)

**Why so energy-intensive?**

Because brain is:
1. **Processing information** (neuron firing, synaptic transmission)
2. **Maintaining memory** (synaptic weight stabilization)
3. **Making decisions** (evaluating options, choosing actions)

These are all **information operations**, and information has energy cost.

### Landauer Limit

Minimum energy to erase 1 bit of information:

$$
E_{\min} = k_B T \ln 2 \approx 3 \times 10^{-21} \text{ J}
$$

(at room temperature)

Brain processes about $10^{16}$ synaptic events per second, if each involves 1 bit, total energy:

$$
E \sim 10^{16} \times 3 \times 10^{-21} \approx 30 \text{ mW}
$$

Actual consumption 20W, meaning **efficiency about 0.15%**—most energy used maintaining structure, fighting entropy increase.

**Physical cost of free will: 20% of brain's energy budget.**

### Cost of Decision-Making

Making decisions consumes more energy than execution.

Experiments:
- Simple reaction (press button when see light): Few brain regions activated
- Complex choice (weighing multiple options): Many brain regions activated, high energy consumption

**Complex decisions consume energy several times that of simple reactions.**

This is why:
- **Decision fatigue** is real (consecutive decisions deplete glucose)
- **Daydreaming is easier** (reduces information processing intensity)
- **Automated habits save effort** (reduces active decisions)

**Freedom is expensive—you must pay cost for each choice.**

---

## Act IV: Limitations of Determinism

Free will advocates often encounter a rebuttal:

**"Laplace's Demon"** — If there's an omniscient demon knowing all particles' positions and velocities in universe, it can predict everything (including your "choices"). So freedom is illusion.

### Quantum Uncertainty

First limitation: **Heisenberg uncertainty principle**

$$
\Delta x \cdot \Delta p \geq \frac{\hbar}{2}
$$

You cannot simultaneously precisely know position and momentum—**perfect prediction impossible**.

But determinists rebut: Uncertainty is just randomness, not freedom.

### Chaos Amplification

Second limitation: **Quantum chaos**

Tiny quantum fluctuations, exponentially amplified through chaotic systems:

$$
\Delta x(t) \sim \Delta x(0) \cdot e^{\lambda_L t}
$$

Even if initial error extremely small, quickly becomes macroscopically unpredictable.

**Brain is chaotic system—nonlinear dynamics of neural networks.**

Butterfly effect: Quantum fluctuation of one neuron may change your decision.

But determinists rebut again: Chaos is also deterministic, just sensitive.

### Self-Referential Undecidability

Third limitation (most profound): **Undecidability of self-referential systems**

If you try to predict your own decision:
- Your prediction affects your decision
- After decision changes, prediction fails
- Update prediction, decision changes again
- **Infinite recursion**

Corollary of Gödel's incompleteness theorem: **Self-referential systems cannot completely self-predict**.

**You cannot predict your entire future, even with perfect information—because prediction behavior itself changes future.**

This isn't ignorance, but **logical necessity**.

---

## Act V: Levels of Freedom

Freedom is not binary (yes/no), but **spectrum**.

### Level 0: No Freedom

- Stone: $I(M \to Y) = 0$ (no action affects future)
- Pendulum: Completely deterministic, no choice space

### Level 1: Reactivity

- Thermostat: $I > 0$ but very small (on/off two states)
- Simple reflex: Stimulus → fixed reaction

**Has causal influence, but choice space almost zero.**

### Level 2: Adaptability

- Bacterial chemotaxis: Adjust movement direction based on gradient
- $\mathcal{E}_k$ small but non-zero (multiple strategies)

**Limited choice space, simple optimization.**

### Level 3: Learning

- Animal learning: Improve strategies through trial and error
- $I(M \to Y)$ increases (actions affect future environment)

**Choice space expands with experience.**

### Level 4: Planning

- Tool use: Primates, birds, octopuses
- Predict future, plan multi-step actions
- $\mathcal{E}_k$ significant ($k$-step lookahead)

**Long-term causal influence.**

### Level 5: Meta-Cognition

- Humans: Think about thinking
- Evaluate reasons for choices
- Change own decision rules

**Highest level: Choose how to choose.**

$$
I(M_{\text{meta}} \to M_{\text{object}}) > 0
$$

**You not only choose actions, but choose decision rules—this is meta-freedom.**

---

## Act VI: Physical Basis of Compatibilism

Now we can understand why compatibilism makes sense.

### Frankfurt Case

Philosopher Frankfurt proposed:

You want to do $A$, and you do $A$. But if you wanted to do $B$, a controller would force you to do $A$.

**Do you have freedom?**

- Incompatibilists say: No (no other possibility)
- Compatibilists say: Yes (you act according to your will)

### GLS Answer

Key is distinguishing:

**Actual freedom**: Future you can actually change
**Counterfactual freedom**: If you did something else, what would happen

Physics only cares about actual: $I(M \to Y)$

If your actual action $M$ affects actual future $Y$ ($I > 0$), you have **actual freedom**.

As for "if you chose $B$"—this is **counterfactual**, not within scope of physical measurement.

**Compatibilism is right: As long as your actions truly change future, you have freedom—even if there's a controller in other possible worlds.**

---

## Act VII: Enhancing Your Freedom

If freedom is $I(M \to Y)$ and $\mathcal{E}_k$, how to enhance freedom?

### Strategy 1: Expand Information Channels

$$
I(M \to Y) \leq \text{Channel Capacity}
$$

Your freedom is limited by capacity of "action → observation" channel.

Enhancement methods:
- **Learn skills**: Increase available action space (learn driving, programming, instruments...)
- **Expand perception**: Increase observation dimensions (learn new languages, understand new fields...)

**Skills = expanding causal influence.**

### Strategy 2: Extend Time Horizon

$$
\mathcal{E}_k = \max I(A^k; S_{k+1})
$$

Larger $k$, farther lookahead, higher degree of freedom.

Enhancement methods:
- **Planning ability**: Consider long-term consequences (saving, learning, health investment...)
- **Delayed gratification**: Resist immediate temptations, pursue long-term goals

**Patience = freedom across time.**

### Strategy 3: Reduce Constraints

Freedom is limited by:

$$
I(M \to Y | \text{Constraints})
$$

More constraints, less freedom.

Reduction methods:
- **Economic freedom**: Escape poverty (more choice space)
- **Health freedom**: Maintain physical health (action capability)
- **Cognitive freedom**: Overcome biases, fears (psychological constraints)

**Constraints are cages of freedom.**

### Strategy 4: Increase Energy Supply

Remember energy constraint:

$$
\langle W \rangle + k_B T \langle I \rangle \geq \Delta F
$$

More energy = more information processing = more freedom.

Methods:
- **Adequate sleep**: Restore brain energy
- **Balanced nutrition**: Provide glucose
- **Physical exercise**: Improve metabolic efficiency

**Fatigue reduces freedom—your decision quality declines.**

---

## Act VIII: Moral Responsibility

If freedom has degree, how to define moral responsibility?

### Traditional Dilemma

- If humans have no freedom, how to hold responsible? ("He couldn't help it")
- If humans have absolute freedom, why are genes, environment so influential?

### GLS Answer

Responsibility proportional to $I(M \to Y)$:

$$
\text{Responsibility} \propto I(M \to \text{Outcome})
$$

**Your responsibility for outcome equals causal contribution of your actions to outcome.**

This explains:
- **Children have lighter responsibility**: $I$ small (cognition immature, weak lookahead ability)
- **Mental illness reduces responsibility**: $I$ reduced by pathological constraints
- **Coercion/threat reduces responsibility**: External constraints compress choice space

**Responsibility is continuous, proportional to causal influence—this matches legal practice (like "diminished responsibility").**

### Meaning of Punishment

If freedom is limited, does punishment still have meaning?

GLS answer: **Punishment is information feedback, enhancing future $I(M \to Y)$.**

- **Deterrence**: Increase expected cost of crime, change decision function
- **Rehabilitation**: Provide new information, expand choice space
- **Isolation**: Temporarily reduce $I(M \to Y)$ (reduce social influence)

**Punishment isn't revenge, but system optimization—adjusting distribution of individual causal influence.**

---

## Act IX: Collective Freedom

Freedom is not only individual property, but also collective property.

### Society's Degree of Freedom

$$
I_{\text{collective}} = I(M^{\text{society}} \to Y^{\text{society}})
$$

Society's freedom = influence of collective actions on collective future.

This depends on:
- **Information flow**: Freedom of speech, press freedom (expand diversity of $M$ and $Y$)
- **Power dispersion**: Democratic systems (increase number of effective actors)
- **Education**: Enhance individual $\mathcal{E}_k$ (collective wisdom)

**Problem with authoritarian societies: Information concentrated in few, $I_{\text{collective}}$ very small—society loses adaptive capacity.**

### Technology and Freedom

How does technology affect freedom?

**Double-edged sword:**

**Enhance freedom:**
- Internet: Information acquisition cost ↓, $I(M\to Y)$↑
- Automation: Free time, choice space↑
- AI assistance: Cognitive ability↑, $\mathcal{E}_k$↑

**Limit freedom:**
- Algorithmic recommendations: Shrink information window, $I$↓
- Surveillance: Action space constrained
- Addictive design: Hijack decision systems

**Net effect of technology depends on design—does it expand or compress human $I(M \to Y)$?**

---

## Act X: Ultimate Freedom

Finally, philosophical question:

### Can You Choose Your Own Goals?

Traditional free will discussion: You can choose actions.

Deeper question: **Can you choose desires themselves?**

- You want sweets (genetically determined)
- You want recognition (evolutionarily shaped)
- You want to understand world (culturally instilled?)

**If desires aren't chosen by you, is your "freedom" real?**

### Meta-Freedom

GLS answer: **You have limited meta-freedom—can partially change objective function.**

$$
I(M_{\text{meta}} \to \text{Goals}) > 0
$$

Evidence:
- Meditation can change emotional responses
- Cognitive behavioral therapy can change beliefs
- Philosophical reflection can change values

**You cannot completely rewrite brain (constrained by biology), but can adjust at margins—this is meta-freedom.**

### Highest Freedom: Accepting Constraints

Stoicism says: **Freedom is not absence of constraints, but understanding constraints and choosing within them.**

$$
\text{True Freedom} = \max_{M \in \text{Possible}} I(M \to Y | \text{Understanding Constraints})
$$

**Freedom isn't "do whatever you want," but "maximize causal influence within possible range".**

You cannot fly (physical constraint), but can choose:
- Learn flying (pilot aircraft)
- Learn skydiving (brief flying sensation)
- Learn physics (understand why can't fly)

**Accept constraints, optimize within constraints—this is mature freedom.**

---

## Take-Home Thoughts

Right now, you're reading this article.

You can choose:
- Continue reading (action $M_1$)
- Stop and think (action $M_2$)
- Close page (action $M_3$)

**Is this choice real?**

Physics says: **Yes—as long as your choice can change your future** $(I(M \to Y) > 0)$.

If you continue reading, you'll gain more information, change thinking patterns, affect future behavior.
If you stop, you'll maintain current cognitive state.

$$
I(\text{finish article} \to \text{future you}) \neq I(\text{don't read} \to \text{future you})
$$

**This inequality is your freedom.**

And this freedom has cost:
- Your brain is consuming glucose (energy cost)
- Your attention is focusing (opportunity cost)
- Your neural networks are adjusting (information processing cost)

**You pay for freedom—every choice burns thermodynamic free energy.**

But this also means: **Your choices are real, have physical consequences, can change the world.**

**Freedom is not illusion—it's physical reality with cost.**

---

*Next (Final): "The Geometric Map of Meaning: Information Geometry of Value, Purpose, and Existence"*

*We will see that ethical values, meaning of life, purpose of existence are neither emptiness nor subjective, but objective structures on information geometric manifolds.*

