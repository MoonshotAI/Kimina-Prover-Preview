# Kimina-Prover Preview: Towards Large Formal Reasoning Models with Reinforcement Learning

<p align="center">
  <b> Numina & Kimi Team</b></a>
</p>

<div align="center">
  <a href="Kimina_Prover_Preview.pdf"><img src="images/logo_kn.png" height="16" width="36" style="vertical-align:middle"><b> Tech Report</b></a>  |  
  <a href="https://huggingface.co/collections/AI-MO/kimina-prover-preview-67fb536b883d60e7ca25d7f9"><img src="https://huggingface.co/front/assets/huggingface_logo-noborder.svg" height="16" width="16" style="vertical-align:middle"><b> HuggingFace</b>
  </a>
</div>
<br>


📈 Introducing **Kimina-Prover Preview**, the first large formal reasoning model that can reason in a human-like way and prove mathematical theorems rigorously in the Lean 4 language.

- **SotA performance**: It achieves 80%+ pass rate on miniF2F benchmark for the first time, among all published results. It outperforms all prior works such as BFS-Prover (72.9%, previous SotA), Hunyuan-Prover, DeepSeek-Prover and Leanabelle-Prover by a large margin.
- **High Sample Efficiency**: Kimina-Prover Preview delivers strong results even with very small sample budget, e.g.  68.85% on pass@32 and 65.16% on pass@8.
- **Open Source**: We release two distilled versions of our RL model and one autoformalization model on [Hugging Face](https://huggingface.co/collections/AI-MO/kimina-prover-preview-67fb536b883d60e7ca25d7f9). We also release a rectified version of miniF2F-test as our model helps to identify at least 5 problems in the miniF2F-test dataset that were wrongly formalized. All proofs found by Kimina-Prover Preview in miniF2F-test are also released in [this repo](minif2f_test_solved). 



<p align="center">
    <img width="75%" src="images/main_result.png">
</p>


## Key Ingredients of Kimina-Prover Preview

<p align="center">
  <img src="images/rl-pipeline.png" alt="The Reinforcement Learning Training System for LLM" width="75%" style="vertical-align:middle">
</p>

Some key ingredients about the design and training of Kimina-Prover Preview are listed as follows.


- **Whole-proof Generation Enhanced by RL**: All proofs are generated without any prover feedback during training and test. And consistent with the results of Kimi k1.5, we show that strong performance can be achieved without relying on more complex techniques such as Monte Carlo tree search, value functions, and process reward models.
-  **Model Size Scaling**: Our experiments demonstrate performance scaling with model size, a trend previously unobserved for neural theorem provers. Specifically, a model size of 72B is applied and much stronger performance is obtained compared to models of smaller size.
- **Long Context Scaling**: We adopt a context window of RL up to 32K tokens for training and inference, which is the longest context used in the neural theorem proving community.
- **Distinct Reasoning Style**: We carefully design a reasoning style that we call *Formal Reasoning Pattern* that bridges the gap between formal verification and informal mathematical intuition.
  <p align="center">
      <img src="images/formal-reasoning-pattern.png" alt="The Reinforcement Learning Training System for LLM" width="30%" style="vertical-align:middle">
  </p>

