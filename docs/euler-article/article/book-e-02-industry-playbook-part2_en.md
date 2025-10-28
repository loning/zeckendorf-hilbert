# Volume E-2 | Practice Handbook (Part 2): City, Finance, AI

> This is an English translation of [中文原文](book-e-02-industry-playbook-part2.md)

## Opening: From Individual to System

In the previous volume, we discussed applications at individual and family levels.

This volume discusses system-level applications: city, finance, AI—areas that seem distant but profoundly impact our lives.

Let's begin.

---

## Scenario Four | City: How to Make Cities More Resilient

### Problem: Why Do Some Cities "Collapse at the Slightest Problem"?

Have you seen cities like this:
- When heavy rain comes, traffic paralyzes.
- When a certain market closes, nearby residents have difficulty buying groceries.
- When a pandemic starts, the entire city falls into chaos.

This isn't "natural disaster," but the city lacking "resilience."

### Solution: Three Steps to Improve City Resilience

**Step One: Spectral Diagnosis (Find City's "Weak Links")**

View the city as a network:
- Nodes are functional points (communities, hospitals, schools, transportation hubs, commercial areas).
- Connections are channels (roads, buses, subways, walkways).

Then, check this network's "connectivity":
- If a certain node fails (like a subway station closes), will it cause widespread paralysis?
- If a certain connection breaks (like a main road under construction), is there no alternative route?

Those "one failure causes total paralysis" nodes and connections are weak links.

**Step Two: Add Edges/Adjust Weights (Increase Redundancy and Diversity)**

After finding weak links, two ways to strengthen:
- **Add edges**: Add new connections. For example, between two isolated communities, build a new road.
- **Adjust weights**: Improve existing connection capacity. For example, widen narrow road, change one-way to two-way.

The key is: don't only focus on "busiest traffic" places, but on "most easily broken" places.

**Step Three: Public Window Positioning (Build Cross-Group Spaces at "Bottlenecks")**

In cities, different groups are often isolated:
- Wealthy areas and working areas don't interact.
- Young people and elderly each have their own activity ranges.
- Locals and outsiders never meet.

This isolation leads to city "fragmentation."

Solution is: at different groups' "intersections," establish "public windows":
- Libraries, parks, community centers, let different groups have opportunities to interact.
- Hold cross-group activities (like community sports meets, markets, volunteer activities).

### Example: Improving Resilience of an Old City District

- **Spectral Diagnosis**: Discover this district only has one main road, once under construction or congested, entire area paralyzes.
- **Add Edges**: Between residential area and commercial area, build a walkway and bicycle path as alternative route.
- **Public Window**: At intersection of old resident area and new resident area, build a community library, hold book clubs and skill exchange activities.

### Key Indicators

- Network connectivity improves (spectral gap increases, mixing time shortens).
- Traffic congestion frequency decreases (queue waiting time drops).
- Cross-group mixing degree improves (contact frequency between different groups increases).

---

## Scenario Five | Finance: How to Identify "Bubbles"

### Problem: Why Do People Always "Buy at the Peak"?

Have you seen this scenario:
- A certain asset keeps soaring, everyone shouts "will rise more," you fear missing opportunity, buy at peak, result immediately crashes.

Why? Because you didn't identify the "bubble."

### Solution: Three Steps to Identify Bubbles

**Step One: No-Arbitrage Health Check (Check "Is Price Reasonable")**

An asset's reasonable price should equal "present value of all future returns."

For example, a stock's reasonable price should equal "present value of all future dividends."

If its actual price far exceeds this reasonable price, there might be a "bubble."

A simple test method:
- Calculate, at current price, how many years until you "break even" (returns cover cost)?
- If answer is "over 50 years" or "impossible to break even," be alert.

**Step Two: Premium Estimation (Find Root of "Unreasonableness")**

If price is obviously too high, ask yourself:
- Is this premium due to "scarcity" (like school district housing, Bitcoin cap)?
- Or due to "emotion" (like everyone thinks it will rise more)?

If the former, premium might be reasonable; if the latter, it's a bubble.

**Step Three: Bubble Identification (Check Price-Fundamentals Deviation)**

Do a simple cointegration test:
- Put asset's price curve and its "fundamentals" (like company profits, housing rent, gold demand) together.
- If price long-term follows fundamentals fluctuation, relatively healthy.
- If price at a certain stage "detaches" from fundamentals, rises sharply, that's a bubble sign.

### Example: Judging Whether a Stock Is Overvalued

- **No-Arbitrage Health Check**: This company pays 100 yuan dividend annually, current stock price 10,000 yuan. At 5% discount rate, reasonable price should be around 2,000 yuan. Current price is 5 times reasonable price, obviously overvalued.
- **Premium Analysis**: Overvaluation reason is not company business breakthrough, but "everyone thinks it will rise more" (emotion-driven).
- **Bubble Identification**: Put stock price and company profit on same graph, discover in the past year, stock price rose 10 times, but profit only rose 20%. Obviously deviates.

Conclusion: This stock is likely in a bubble, not suitable to buy.

### Key Indicators

- Price-fundamentals deviation degree (smaller the healthier).
- Emotion indicators (like search heat, discussion heat) abnormally high (if abnormally high, alert to bubble).
- Holding this asset's "break-even time" is it reasonable (generally, 10-20 years acceptable, over 30 years be alert).

---

## Scenario Six | AI: How to Ensure AI "Aligns" with Human Values

### Problem: Why Does AI "Learn Bad Things"?

Have you seen news like this:
- A certain chatbot learned to curse.
- A certain recommendation algorithm only recommends extreme content (because extreme content more eye-catching).
- A certain self-driving system performs perfectly in tests, but dangerous in real scenarios.

Why? Because AI's "goal" and human "values" aren't aligned.

### Solution: Three-Step Alignment Method

**Step One: Alignment (Clarify "What Is Good")**

Don't only give AI a simple goal (like "highest click rate"), but a "multi-objective optimization":
- User satisfaction (long-term retention, not just short-term clicks).
- Content quality (valuable, not just sensational).
- Fairness (different groups all served, not just serving "high-value users").

Then, use "small-step adjustment" method to gradually bring AI closer to these goals:
- Don't make big changes all at once, but fine-tune a bit each time, observe effects.
- If a certain adjustment causes "unexpected side effects" (like sacrificing fairness), immediately rollback.

**Step Two: Explainability (Ensure AI's Decisions "Can Be Understood")**

If AI is a "black box," you can't know why it made this decision, also can't test if it "learned bad things."

So, make AI's decisions "explainable":
- Can use simple logic to reproduce over 80% of decision results.
- If changing a certain key factor, AI's decision changes accordingly (causal consistency).

A simple test:
- Have AI explain "why recommend this content to this user."
- If AI can only say "because model calculated this way," that's problematic.
- If AI can say "because this user previously watched similar content, and this content is high quality, well-reviewed," that's relatively explainable.

**Step Three: Anti-Hallucination (Avoid AI "Spouting Nonsense")**

AI sometimes "seriously spouts nonsense":
- Fabricates nonexistent facts.
- In uncertain situations, gives overly confident answers.

Solution:
- Have AI learn to "refuse to answer": if uncertain, say "I don't know," not "make things up."
- Add "fact verification" step: for key information, AI must provide sources, not just conclusions.

### Example: Optimizing a Content Recommendation System

- **Alignment**: Goal is not just "click rate," but "click rate + user satisfaction + content diversity." Fine-tune weights weekly, observe if long-term retention improves.
- **Explainability**: When recommending, display "recommendation reason" (like "because you previously liked sci-fi novels, this book has high ratings").
- **Anti-Hallucination**: For sensitive topics (like health, law), if AI is uncertain, display "suggest consulting professionals," not give irresponsible advice.

### Key Indicators

- Long-term retention rate improves (indicates users truly satisfied, not just "induced clicks").
- Different groups' satisfaction gap narrows (indicates fairness improves).
- User complaint rate drops (indicates "learned bad things" cases reduce).

---

## Conclusion: From Scenarios to Methods

These three scenarios cover system-level applications:

- **City**: Use "spectral diagnosis—add edges adjust weights—public windows" to improve resilience.
- **Finance**: Use "no-arbitrage health check—premium analysis—bubble identification" to avoid buying at peak.
- **AI**: Use "alignment—explainability—anti-hallucination" to ensure AI serves humanity, not "loses control."

These scenarios seem very "high-end," but actually the underlying logic is simple:

- Find system's weak links, enhance connectivity and redundancy.
- Check if price is reasonable, alert to bubbles detached from fundamentals.
- Ensure AI's goals align with human values, and are explainable, controllable.

From individual to system, from family to city, from education to AI, these methods' underlying logic is connected.

Understand this logic, you can find clear leverage points in complex systems.

And this is wisdom's application at the system level.
