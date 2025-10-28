# Volume F-2 | Experimental Standards (Advanced): Nine Advanced Tools

> This is an English translation of [中文原文](book-f-02-experimental-standards-continued.md)

## Opening: From Foundation to Advanced

In the previous volume, we learned five foundational quality inspection tools.

This volume continues deeper, learning nine advanced tools.

These tools will help you inspect: fairness, timing, risk, value, ethics.

Let's begin.

---

## Tool Six | Mirror Audit: Examine Fairness

### Problem: How to Judge If a Rule Is Fair?

You made a rule, you think it's quite reasonable, but others complain "unfair."

Who's right, who's wrong?

### Tool's Core: Permutation Test

A simplest fairness test: **Swap two affected groups, see if the rule still holds**.

If after swapping, rule is still acceptable, it's fair. If after swapping, you yourself feel "this is unreasonable," there's a problem.

### How to Use

**Step One: List Affected Groups**
This rule, who does it affect? Divide them into several groups (like management, regular employees; old employees, new employees; locals, outsiders).

**Step Two: Do Permutation Test**
Imagine if two groups swap positions:
- If you were the unfavorably treated side, could you accept?
- If you were the beneficiary, would you feel "this is deserved," or "this is privilege"?

**Step Three: Calculate Symmetry**
If there's data, can calculate "symmetry deviation degree":
- Apply rule to groups A and B, record results.
- Swap A and B, apply rule again, see if results are symmetric.
- If severely asymmetric, rule has favoritism.

### Example: Evaluate a Promotion Standard

A company's promotion standard is "work years + performance."

- **Permutation test**: Swap "old employees" and "new employees," see if standard still reasonable.
- **Discover problem**: Old employees get automatic points for "long tenure," even with average performance can be promoted; new employees even with outstanding performance, suppressed due to short tenure.
- **Improvement**: Adjust weights, lower "tenure" weight, raise "performance" and "potential" weights, give both old and new employees fair promotion paths.

### Key Indicators

- Different groups' satisfaction gap narrows.
- Cases complaining "unfair" reduce.
- Symmetry test pass rate improves.

---

## Tool Seven | Sacred Time Detection: Identify Key Timing

### Problem: Why Are Some Opportunities "Fleeting"?

Have you had this regret:
- A certain opportunity, didn't seize at the time, afterwards discovered "that was a golden window."
- A certain decision, hesitated too long, when you made up your mind, timing had passed.

### Tool's Core: Phase Alignment Detection

"Key timing" (sacred time) refers to: multiple independent factors simultaneously align at a certain time point, forming a special opportunity window.

How to identify? Look at "phase alignment degree."

### How to Use

**Step One: List Key Factors**
For this to succeed, which factors need to be present simultaneously?
- For example startup: your preparation, market demand, resources in place, era trends.

**Step Two: Track Each Factor's "Phase"**
Each factor, at what stage?
- Your preparation: just starting (phase 0°), accumulating (90°), approaching maturity (180°), or already past peak (270°)?
- Market demand: budding, explosive, saturated?
- Resources: scarce, abundant, excessive?

**Step Three: Detect Alignment Degree**
If multiple factors' phases simultaneously approach "optimal value" (usually between 180°-270°, i.e., "mature but not past peak"), that's "sacred time."

### Example: Judge Whether to Change Jobs

- **Your preparation**: At current company three years, skills mature, but starting to enter "comfort zone," growth slowing (phase 200°).
- **Market demand**: Your skills in external market have strong demand, right in recruitment peak (phase 180°).
- **Personal resources**: Savings sufficient, family stable, have certain risk tolerance (phase 190°).

Three factors simultaneously in "maturity period," high alignment degree, this is the "sacred time" to change jobs.

### Key Indicators

- Multi-factor alignment degree (higher closer to "sacred time").
- Opportunity window width (how long alignment state can last).
- Retrospective verification (looking back, whether indeed seized best timing).

---

## Tool Eight | Pointer Basis and Spectral Gap Estimation: Evaluate Sample Complexity

### Problem: Why Are Some Conclusions "Sample Too Small, Unreliable"?

You did a survey, interviewed 10 people, concluded: "Most people like A."

But others question: "You only asked 10 people, can they represent everyone?"

How do you respond?

### Tool's Core: Sample Complexity Calculation

To get reliable conclusions, how large a sample is needed? This isn't "more is better," but has a calculable lower bound.

Key factor is "spectral gap":
- If people's views are very dispersed (small spectral gap), you need a larger sample.
- If people's views are relatively concentrated (large spectral gap), needed sample is smaller.

### How to Use

**Step One: Estimate Spectral Gap**
Do a small-scale pilot survey (like 20-30 people), look at view "concentration":
- If 90% hold same view, spectral gap is large.
- If views are all over the place, no obvious mainstream, spectral gap is small.

**Step Two: Calculate Needed Sample**
Use a simple formula to estimate:
- Needed sample ≈ (tolerance rate squared) ÷ spectral gap

For example:
- You want tolerance rate 10% (i.e., estimation error not exceeding 10%), spectral gap is 0.5, needed sample ≈ (0.1×0.1) ÷ 0.5 = 0.02, i.e., 2% of total.
- If total is 1000 people, need 20 people; if total is 10,000 people, need 200 people.

**Step Three: Verify Credibility**
If your actual sample exceeds "needed sample," conclusion is relatively reliable. If less than, must state in report "sample size insufficient, for reference only."

### Example: Evaluate Product Satisfaction

- **Pilot survey**: Interviewed 30 users, found 80% satisfied, 20% dissatisfied, views relatively concentrated, spectral gap estimated 0.6.
- **Calculate**: Want tolerance rate 10%, needed sample ≈ (0.1×0.1) ÷ 0.6 ≈ 0.017, i.e., 1.7% of total users.
- **Verify**: Total users 5000, need about 85 people. Actually interviewed 100, sample size sufficient, conclusion reliable.

### Key Indicators

- Whether sample size reaches "needed sample" lower bound.
- When retrospectively checking, whether conclusion still holds (reproducibility).

---

## Tool Nine | Feng Shui SNR Quantification: Evaluate Information Quality

### Problem: Why Is Some Information "Seems Useful, Actually All Noise"?

You see many "success learning articles," "investment secrets," "health remedies" online.

Which are truly valuable signals, which are just noise?

### Tool's Core: Signal-to-Noise Ratio (SNR)

Information's value is not looking at "information amount," but looking at "useful signal" and "noise" ratio.

- If SNR is high (like >10), this information is very valuable.
- If SNR is low (like <2), most of this information is noise, limited value.

### How to Use

**Step One: Identify "Useful Signal"**
This information, can it answer your core question? Can it guide your specific actions?
- If yes, it's "signal."
- If only "sounds reasonable," but don't know how to use, might just be "noise."

**Step Two: Identify "Noise"**
This information, how much is:
- Nonsense (like "success needs effort" - correct but useless words).
- Contradictions (like logical conflicts).
- Irrelevant (like content completely unrelated to your problem).

**Step Three: Calculate SNR**
- SNR = useful signal weight ÷ noise weight
- If you read a 1000-word article, 100 words are truly useful advice, other 900 words are nonsense, SNR ≈ 100 ÷ 900 ≈ 0.11, very low.

### Example: Evaluate a "Success Learning" Video

- **Useful signal**: Mentioned "write daily journal," "regular review" two specific methods (10% content).
- **Noise**: Lots of inspirational talk,励志故事, personal experiences, no actionability (90% content).
- **SNR**: 10 ÷ 90 ≈ 0.11, very low, not worth spending time.

Compare: a technical tutorial:
- **Useful signal**: Detailed steps, code examples, common errors (80% content).
- **Noise**: Small amount of chat and background (20% content).
- **SNR**: 80 ÷ 20 = 4, relatively high, worth learning.

### Key Indicators

- Information's actionability (proportion that can guide specific actions).
- Actual improvement after learning (not "felt good hearing it, but nothing changed").

---

## Tool Ten | Miracle Tilt Experiment: Control Low-Probability Events

### Problem: How to Increase "Winning" Probability?

Some things have inherently low success probability (like startups, writing fame, getting into prestigious schools).

What you can do is "increase attempt frequency." But problem is: if each attempt cost is too high, you can't last a few times before bankruptcy.

### Tool's Core: Low-Cost High-Frequency Trial-and-Error

"Miracles" aren't waited for, but "manufactured" through "systematically increasing trial-and-error opportunities."

Key is: each trial-and-error cost must be low enough, so you can bear enough failures until success.

### How to Use

**Step One: Estimate Single Success Probability**
This thing, what's single attempt success probability?
- For example, submitting an article for acceptance might be 10%.

**Step Two: Design Minimum Viable Experiment**
How to reduce single attempt cost to minimum?
- Don't "go all out" from the start (like spend three months writing a long article), but "quickly verify" (like spend three days writing a short article, see feedback).

**Step Three: Calculate Needed Attempts**
If you want "at least one success" probability to reach 90%, need how many attempts?
- Formula: Needed attempts ≈ -ln(1-target probability) ÷ single success probability
- For example, single success probability 10%, want total success probability 90%, need about 23 attempts.

**Step Four: Control Variance**
Don't let any single failure "break bones," but let each failure be "bearable."

### Example: Improve Article Acceptance Probability

- **Single probability**: Submission acceptance probability about 10%.
- **Minimum experiment**: Write one short article weekly (cost: 3 hours weekly), submit to different platforms.
- **Needed attempts**: To reach 90% total success probability, need to submit about 23 times, i.e., half a year.
- **Variance control**: Each failure, only lose 3 hours, doesn't affect life and work, can continue.

### Key Indicators

- Single cost low enough (can bear multiple failures).
- Cumulative success probability reaches target (like 90%).
- Variance controllable (won't "collapse" due to any single failure).

---

## Tool Eleven | Ethical Net Increase Accounting: Quantify Good and Evil

### Problem: How to Judge If a Decision Is "Good" or "Evil"?

Many decisions, short-term look good, long-term might be harmful.

For example:
- To complete performance, squeeze employees, short-term performance improves, long-term team collapses.
- To save money, lower product quality, short-term profit increases, long-term reputation collapses.

How to judge these decisions' "ethical value"?

### Tool's Core: Net Increase = Benefit - Cost

A decision is "good" or "evil," don't look at motive, look at result:
- If this decision makes system's "stability" net increase (benefit > cost), it's "good."
- If it makes system's "stability" net decrease (benefit < cost), it's "evil."

### How to Use

**Step One: List Benefits**
This decision, what benefits did it bring?
- For different groups (employees, customers, shareholders, society) respectively bring what?

**Step Two: List Costs**
This decision, what costs were paid?
- Not only look at "explicit costs" (like money, time), also look at "implicit costs" (like trust, health, long-term capability).

**Step Three: Calculate Net Increase**
Net increase = Benefit - Cost × Shadow scale
- Shadow scale: "conversion coefficient" of different costs. For example, health's shadow scale is very high, sacrificing health for money often isn't worth it.

**Step Four: Long-term Tracking**
Short-term "net increase" isn't necessarily long-term "net increase." Must track at least one year, see this decision's long-term impact.

### Example: Evaluate "996 Work System"

- **Benefit**: Short-term performance improves, project delivered on time.
- **Cost**: Employee health damaged, turnover rate rises, innovation capability drops, company reputation damaged.
- **Net Increase Calculation**:
  - Short-term, performance improvement brings benefit > overtime cost, net increase positive.
  - Long-term, turnover rate rise causes recruitment and training costs to soar, team instability causes efficiency drop, reputation damage causes excellent talent unwilling to join, net increase negative.
- **Conclusion**: This is short-term "good," long-term "evil" decision, unsustainable.

### Key Indicators

- Long-term net increase (not just short-term).
- Net increase distribution among different groups (can't just benefit one side, harm others).
- Sustainability (can this net increase be maintained long-term).

---

## Tool Twelve | Consensus Propagation Optimizer: Improve Alignment Efficiency

### Problem: Why Do Some Teams "Hold Many Meetings, But Still No Consensus"?

Have you seen teams like this:
- Meet weekly, each time discuss same problem, but never have conclusion.
- During meetings everyone nods, after meetings each does their own thing, no real alignment.

### Tool's Core: Optimize Information Propagation Path

Consensus isn't achieved by "more meetings," but by optimizing "information propagation path":
- Which people need deep alignment?
- Which people only need to know conclusions?
- Through what sequence does information propagate most efficiently?

### How to Use

**Step One: Draw Team Network Graph**
- Nodes are people, connections are "need alignment" relationships.
- Weights are "alignment importance" (like between core decision-makers, weight highest).

**Step Two: Identify "Critical Path"**
- Which people's alignment is "must complete first"?
- Which people's alignment can "proceed in parallel"?

**Step Three: Optimize Meeting Structure**
- Don't have everyone attend all meetings (waste time).
- First have "core decision-makers" deeply align (small scope, deep discussion).
- Then have "executors" understand conclusions (large scope, quick sync).

**Step Four: Test Alignment Degree**
After meeting, spot-check several people, ask them:
- What's our core decision?
- What will you do next?

If answers consistent, alignment succeeded. If answers all over the place, meeting ineffective, must adjust.

### Example: Optimize Product Team Meetings

- **Network graph**: Core is product manager, tech lead, design lead, they need deep alignment; developers, designers only need to know conclusions and division of labor.
- **Before optimization**: Everyone meets weekly, discusses all details, 2 hours, low efficiency.
- **After optimization**:
  - Core three hold 30-minute meeting weekly, deeply align direction and priorities.
  - After alignment, each holds 15-minute meeting with their team, sync conclusions and division of labor.
  - Everyone holds bi-weekly all-hands meeting, quickly go through progress, 30 minutes.
- **Result**: Total meeting time reduced 50%, but alignment effect improved (spot-check found everyone's understanding of core decisions consistent from 60% to 90%).

### Key Indicators

- Meeting time drops, but alignment degree improves.
- Decision-to-execution delay shortens (everyone understands and starts executing faster).
- Repeated discussion frequency reduces (won't "hold many meetings, still discussing same problem").

---

## Tool Thirteen | Aliasing Early Warning: Online Monitor Information Quality

### Problem: How to Discover Problems Before Information "Already Chaotic"?

Often, when you discover "information is chaotic," already too late to fix.

Is there a way to alert when information just starts getting chaotic?

### Tool's Core: Folding Energy Detection

When information from different sources, different times mixes together, produces "folding energy" (i.e., information chaos degree).

If folding energy exceeds threshold, alert.

### How to Use

**Step One: Define Information Sources**
Classify information:
- First-hand information (saw with own eyes, experimental data).
- Second-hand information (others' accounts, media reports).
- Speculative information (hypothesis-based analysis).

**Step Two: Real-time Monitor Mixing Degree**
During discussion and decision process, record:
- Information everyone cites, which category does each belong to?
- Is information from different categories conflated?

**Step Three: Calculate Folding Energy**
If in same argument, multiple sources mixed without clear distinction, folding energy rises.

**Step Four: Trigger Alert**
If folding energy exceeds threshold (like >30%), pause discussion, first clarify information sources.

### Example: Project Retrospective Meeting

- **Scenario**: Team retrospecting "why project delayed."
- **Monitor**: Someone says "client needs changed" (first-hand), someone says "heard client has internal conflicts" (second-hand), someone says "maybe we responded too slowly" (speculation).
- **Folding Energy**: Three types of information mixed, not distinguished, folding energy 40%, exceeds threshold.
- **Alert**: Pause, first clarify: what did client clearly say? What did we hear? What are we speculating?
- **After clarifying**: Discover "client needs changed" is fact, "client internal conflicts" is rumor, "we responded too slowly" is speculation. Refocus on facts, find true root cause.

### Key Indicators

- Folding energy (lower the better).
- Alert trigger frequency (if frequently triggered, team's information management has problems, need to establish standards).
- Decision quality (after clarifying information, decision quality improves).

---

## Tool Fourteen | Calibration Scoreboard: Test Prediction Accuracy

### Problem: Why Are Some People "Always Very Confident, But Often Wrong"?

Some people, when making predictions especially confident: "I'm 100% sure it'll be like this!" Result often wrong.

Some people, very cautious, but also often right.

How to evaluate a person's prediction quality?

### Tool's Core: Probability Calibration

Good predictions not only need "result right," but also "probability accurate."

What does this mean?
- If you say "this has 90% chance of happening," then among all your 90% probability predictions, should have close to 90% actually happened.
- If you often say "90%," but actually only 50% happen, you're overconfident, poorly calibrated.

### How to Use

**Step One: Record Predictions**
Each time making prediction, not only give "will it happen," but also give "occurrence probability" (like 70%).

**Step Two: Group Statistics**
Group all predictions by probability you gave:
- 50%-60% predictions in one group.
- 60%-70% predictions in one group.
- And so on.

**Step Three: Calculate Actual Occurrence Rate**
In each group, what proportion actually occurred?

**Step Four: Compare Calibration Curve**
- If you gave 70% probability predictions, actual occurrence rate also close to 70%, your calibration is good.
- If you gave 70%, but actually only 50% occurred, you're overconfident.
- If you gave 70%, but actually 90% occurred, you're overly cautious.

### Example: Evaluate a Product Manager's Prediction Ability

- **Record**: They made 100 predictions about "feature launch time," each time gave probability.
- **Group**:
  - Gave 70%-80% probability predictions 30 times, actually on-time launch 22 times (73%), well calibrated.
  - Gave 90%-100% probability predictions 20 times, actually on-time launch only 12 times (60%), overconfident.
- **Feedback**: Remind them, when giving "over 90%" predictions, be more cautious, consider if there are overlooked risks.

### Key Indicators

- Calibration curve (closer to diagonal the better).
- Overconfidence index (if often overestimate probability, overconfident).
- Prediction value (well-calibrated predictions have more reference value).

---

## Conclusion: From Quality Inspection to Excellence

These nine advanced tools help you inspect more complex dimensions:

6. **Mirror Audit**: Examine fairness, ensure rules withstand role swap.
7. **Sacred Time Detection**: Identify key timing, seize multi-factor aligned opportunity window.
8. **Pointer Basis and Spectral Gap Estimation**: Evaluate sample complexity, ensure conclusions reliable.
9. **Feng Shui SNR Quantification**: Evaluate information quality, distinguish signal from noise.
10. **Miracle Tilt Experiment**: Control low-probability events, "manufacture miracles" through low-cost high-frequency trial-and-error.
11. **Ethical Net Increase Accounting**: Quantify good and evil, look at long-term net increase not just short-term.
12. **Consensus Propagation Optimizer**: Improve alignment efficiency, reduce ineffective meetings.
13. **Aliasing Early Warning**: Online monitor information quality, alert before chaos.
14. **Calibration Scoreboard**: Test prediction accuracy, distinguish confidence from overconfidence.

From foundation to advanced, these 14 quality inspection tools constitute a complete "quality management system."

With these tools, you can:
- Before decisions, examine fairness and timing.
- During execution, monitor information quality and alignment efficiency.
- After results, evaluate ethical value and prediction accuracy.

This isn't "nitpicking," but "continuous improvement."

Only systems that can self-inspect, self-correct can maintain excellence long-term.

And this is the key from "excellent" to "outstanding."

---

**Series Complete**

From five mirrors and eight natural laws (Volume A), to three gates' twelve laws (Volume B), to judgment standards and deep tools (Volume C), to 24 wisdom concepts (Volume D), to six practice scenarios (Volume E), to 14 quality inspection tools (Volume F).

This system covers the complete chain from individual to organization, from cognition to action, from decision to inspection.

No need for mathematical symbols, no need for professional terminology, only fundamental life wisdom and structured thinking.

Hope these tools can help you find clear direction in the complex world.

May you see the world clearly, while also seeing yourself clearly.
