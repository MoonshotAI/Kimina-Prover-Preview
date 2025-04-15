import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


theorem aime_1984_p7 (f : ℤ → ℤ) (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
    (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) : f 84 = 997 := by
  have h997 : f 997 = 998 := by
    have h1 : f 997 = f (f 1002) := by
      rw [h₁ 997 (by norm_num)]
      norm_num
    have h2 : f 1002 = 999 := by
      rw [h₀ 1002 (by norm_num)]
      norm_num
    rw [h2] at h1
    have h3 : f 999 = f (f 1004) := by
      rw [h₁ 999 (by norm_num)]
      norm_num
    have h4 : f 1004 = 1001 := by
      rw [h₀ 1004 (by norm_num)]
      norm_num
    rw [h4] at h3
    have h5 : f 1001 = 998 := by
      rw [h₀ 1001 (by norm_num)]
      norm_num
    rw [h5] at h3
    rw [h3] at h1
    exact h1

  have h998 : f 998 = 997 := by 
    have h1 : f 998 = f (f 1003) := by 
      rw [h₁ 998 (by norm_num)]
      norm_num
    have h2 : f 1003 = 1000 := by 
      rw [h₀ 1003 (by norm_num)]
      norm_num
    rw [h2] at h1
    have h3 : f 1000 = 997 := by 
      rw [h₀ 1000 (by norm_num)]
      norm_num
    rw [h3] at h1
    exact h1
  
  have h1 : f 84 = f (f 89) := by 
    rw [h₁ 84 (by norm_num)]
    norm_num
  
  have h2 : f 89 = f (f 94) := by 
    rw [h₁ 89 (by norm_num)]
    norm_num
  
  have h3 : f 94 = f (f 99) := by 
    rw [h₁ 94 (by norm_num)]
    norm_num
  
  have h4 : f 99 = f (f 104) := by 
    rw [h₁ 99 (by norm_num)]
    norm_num

  have h5 : f 104 = f (f 109) := by 
    rw [h₁ 104 (by norm_num)]
    norm_num

  have h6 : f 109 = f (f 114) := by 
    rw [h₁ 109 (by norm_num)]
    norm_num

  have h7 : f 114 = f (f 119) := by 
    rw [h₁ 114 (by norm_num)]
    norm_num

  have h8 : f 119 = f (f 124) := by 
    rw [h₁ 119 (by norm_num)]
    norm_num

  have h9 : f 124 = f (f 129) := by 
    rw [h₁ 124 (by norm_num)]
    norm_num

  have h10 : f 129 = f (f 134) := by 
    rw [h₁ 129 (by norm_num)]
    norm_num

  have h11 : f 134 = f (f 139) := by 
    rw [h₁ 134 (by norm_num)]
    norm_num

  have h12 : f 139 = f (f 144) := by 
    rw [h₁ 139 (by norm_num)]
    norm_num

  have h13 : f 144 = f (f 149) := by 
    rw [h₁ 144 (by norm_num)]
    norm_num

  have h14 : f 149 = f (f 154) := by 
    rw [h₁ 149 (by norm_num)]
    norm_num

  have h15 : f 154 = f (f 159) := by 
    rw [h₁ 154 (by norm_num)]
    norm_num

  have h16 : f 159 = f (f 164) := by 
    rw [h₁ 159 (by norm_num)]
    norm_num

  have h17 : f 164 = f (f 169) := by 
    rw [h₁ 164 (by norm_num)]
    norm_num

  have h18 : f 169 = f (f 174) := by 
    rw [h₁ 169 (by norm_num)]
    norm_num

  have h19 : f 174 = f (f 179) := by 
    rw [h₁ 174 (by norm_num)]
    norm_num

  have h20 : f 179 = f (f 184) := by 
    rw [h₁ 179 (by norm_num)]
    norm_num

  have h21 : f 184 = f (f 189) := by 
    rw [h₁ 184 (by norm_num)]
    norm_num

  have h22 : f 189 = f (f 194) := by 
    rw [h₁ 189 (by norm_num)]
    norm_num

  have h23 : f 194 = f (f 199) := by 
    rw [h₁ 194 (by norm_num)]
    norm_num

  have h24 : f 199 = f (f 204) := by 
    rw [h₁ 199 (by norm_num)]
    norm_num

  have h25 : f 204 = f (f 209) := by 
    rw [h₁ 204 (by norm_num)]
    norm_num

  have h26 : f 209 = f (f 214) := by 
    rw [h₁ 209 (by norm_num)]
    norm_num

  have h27 : f 214 = f (f 219) := by 
    rw [h₁ 214 (by norm_num)]
    norm_num

  have h28 : f 219 = f (f 224) := by 
    rw [h₁ 219 (by norm_num)]
    norm_num

  have h29 : f 224 = f (f 229) := by 
    rw [h₁ 224 (by norm_num)]
    norm_num

  have h30 : f 229 = f (f 234) := by 
    rw [h₁ 229 (by norm_num)]
    norm_num

  have h31 : f 234 = f (f 239) := by 
    rw [h₁ 234 (by norm_num)]
    norm_num

  have h32 : f 239 = f (f 244) := by 
    rw [h₁ 239 (by norm_num)]
    norm_num

  have h33 : f 244 = f (f 249) := by 
    rw [h₁ 244 (by norm_num)]
    norm_num

  have h34 : f 249 = f (f 254) := by 
    rw [h₁ 249 (by norm_num)]
    norm_num

  have h35 : f 254 = f (f 259) := by 
    rw [h₁ 254 (by norm_num)]
    norm_num

  have h36 : f 259 = f (f 264) := by 
    rw [h₁ 259 (by norm_num)]
    norm_num

  have h37 : f 264 = f (f 269) := by 
    rw [h₁ 264 (by norm_num)]
    norm_num

  have h38 : f 269 = f (f 274) := by 
    rw [h₁ 269 (by norm_num)]
    norm_num

  have h39 : f 274 = f (f 279) := by 
    rw [h₁ 274 (by norm_num)]
    norm_num

  have h40 : f 279 = f (f 284) := by 
    rw [h₁ 279 (by norm_num)]
    norm_num

  have h41 : f 284 = f (f 289) := by 
    rw [h₁ 284 (by norm_num)]
    norm_num

  have h42 : f 289 = f (f 294) := by 
    rw [h₁ 289 (by norm_num)]
    norm_num

  have h43 : f 294 = f (f 299) := by 
    rw [h₁ 294 (by norm_num)]
    norm_num

  have h44 : f 299 = f (f 304) := by 
    rw [h₁ 299 (by norm_num)]
    norm_num

  have h45 : f 304 = f (f 309) := by 
    rw [h₁ 304 (by norm_num)]
    norm_num

  have h46 : f 309 = f (f 314) := by 
    rw [h₁ 309 (by norm_num)]
    norm_num

  have h47 : f 314 = f (f 319) := by 
    rw [h₁ 314 (by norm_num)]
    norm_num

  have h48 : f 319 = f (f 324) := by 
    rw [h₁ 319 (by norm_num)]
    norm_num

  have h49 : f 324 = f (f 329) := by 
    rw [h₁ 324 (by norm_num)]
    norm_num

  have h50 : f 329 = f (f 334) := by 
    rw [h₁ 329 (by norm_num)]
    norm_num

  have h51 : f 334 = f (f 339) := by 
    rw [h₁ 334 (by norm_num)]
    norm_num

  have h52 : f 339 = f (f 344) := by 
    rw [h₁ 339 (by norm_num)]
    norm_num

  have h53 : f 344 = f (f 349) := by 
    rw [h₁ 344 (by norm_num)]
    norm_num

  have h54 : f 349 = f (f 354) := by 
    rw [h₁ 349 (by norm_num)]
    norm_num

  have h55 : f 354 = f (f 359) := by 
    rw [h₁ 354 (by norm_num)]
    norm_num

  have h56 : f 359 = f (f 364) := by 
    rw [h₁ 359 (by norm_num)]
    norm_num

  have h57 : f 364 = f (f 369) := by 
    rw [h₁ 364 (by norm_num)]
    norm_num

  have h58 : f 369 = f (f 374) := by 
    rw [h₁ 369 (by norm_num)]
    norm_num

  have h59 : f 374 = f (f 379) := by 
    rw [h₁ 374 (by norm_num)]
    norm_num

  have h60 : f 379 = f (f 384) := by 
    rw [h₁ 379 (by norm_num)]
    norm_num

  have h61 : f 384 = f (f 389) := by 
    rw [h₁ 384 (by norm_num)]
    norm_num

  have h62 : f 389 = f (f 394) := by 
    rw [h₁ 389 (by norm_num)]
    norm_num

  have h63 : f 394 = f (f 399) := by 
    rw [h₁ 394 (by norm_num)]
    norm_num

  have h64 : f 399 = f (f 404) := by 
    rw [h₁ 399 (by norm_num)]
    norm_num

  have h65 : f 404 = f (f 409) := by 
    rw [h₁ 404 (by norm_num)]
    norm_num

  have h66 : f 409 = f (f 414) := by 
    rw [h₁ 409 (by norm_num)]
    norm_num

  have h67 : f 414 = f (f 419) := by 
    rw [h₁ 414 (by norm_num)]
    norm_num

  have h68 : f 419 = f (f 424) := by 
    rw [h₁ 419 (by norm_num)]
    norm_num

  have h69 : f 424 = f (f 429) := by 
    rw [h₁ 424 (by norm_num)]
    norm_num

  have h70 : f 429 = f (f 434) := by 
    rw [h₁ 429 (by norm_num)]
    norm_num

  have h71 : f 434 = f (f 439) := by 
    rw [h₁ 434 (by norm_num)]
    norm_num

  have h72 : f 439 = f (f 444) := by 
    rw [h₁ 439 (by norm_num)]
    norm_num

  have h73 : f 444 = f (f 449) := by 
    rw [h₁ 444 (by norm_num)]
    norm_num

  have h74 : f 449 = f (f 454) := by 
    rw [h₁ 449 (by norm_num)]
    norm_num

  have h75 : f 454 = f (f 459) := by 
    rw [h₁ 454 (by norm_num)]
    norm_num

  have h76 : f 459 = f (f 464) := by 
    rw [h₁ 459 (by norm_num)]
    norm_num

  have h77 : f 464 = f (f 469) := by 
    rw [h₁ 464 (by norm_num)]
    norm_num

  have h78 : f 469 = f (f 474) := by 
    rw [h₁ 469 (by norm_num)]
    norm_num

  have h79 : f 474 = f (f 479) := by 
    rw [h₁ 474 (by norm_num)]
    norm_num

  have h80 : f 479 = f (f 484) := by 
    rw [h₁ 479 (by norm_num)]
    norm_num

  have h81 : f 484 = f (f 489) := by 
    rw [h₁ 484 (by norm_num)]
    norm_num

  have h82 : f 489 = f (f 494) := by 
    rw [h₁ 489 (by norm_num)]
    norm_num

  have h83 : f 494 = f (f 499) := by 
    rw [h₁ 494 (by norm_num)]
    norm_num

  have h84 : f 499 = f (f 504) := by 
    rw [h₁ 499 (by norm_num)]
    norm_num

  have h85 : f 504 = f (f 509) := by 
    rw [h₁ 504 (by norm_num)]
    norm_num

  have h86 : f 509 = f (f 514) := by 
    rw [h₁ 509 (by norm_num)]
    norm_num

  have h87 : f 514 = f (f 519) := by 
    rw [h₁ 514 (by norm_num)]
    norm_num

  have h88 : f 519 = f (f 524) := by 
    rw [h₁ 519 (by norm_num)]
    norm_num

  have h89 : f 524 = f (f 529) := by 
    rw [h₁ 524 (by norm_num)]
    norm_num

  have h90 : f 529 = f (f 534) := by 
    rw [h₁ 529 (by norm_num)]
    norm_num

  have h91 : f 534 = f (f 539) := by 
    rw [h₁ 534 (by norm_num)]
    norm_num

  have h92 : f 539 = f (f 544) := by 
    rw [h₁ 539 (by norm_num)]
    norm_num

  have h93 : f 544 = f (f 549) := by 
    rw [h₁ 544 (by norm_num)]
    norm_num

  have h94 : f 549 = f (f 554) := by 
    rw [h₁ 549 (by norm_num)]
    norm_num

  have h95 : f 554 = f (f 559) := by 
    rw [h₁ 554 (by norm_num)]
    norm_num

  have h96 : f 559 = f (f 564) := by 
    rw [h₁ 559 (by norm_num)]
    norm_num

  have h97 : f 564 = f (f 569) := by 
    rw [h₁ 564 (by norm_num)]
    norm_num

  have h98 : f 569 = f (f 574) := by 
    rw [h₁ 569 (by norm_num)]
    norm_num

  have h99 : f 574 = f (f 579) := by 
    rw [h₁ 574 (by norm_num)]
    norm_num

  have h100 : f 579 = f (f 584) := by 
    rw [h₁ 579 (by norm_num)]
    norm_num

  have h101 : f 584 = f (f 589) := by 
    rw [h₁ 584 (by norm_num)]
    norm_num

  have h102 : f 589 = f (f 594) := by 
    rw [h₁ 589 (by norm_num)]
    norm_num

  have h103 : f 594 = f (f 599) := by 
    rw [h₁ 594 (by norm_num)]
    norm_num

  have h104 : f 599 = f (f 604) := by 
    rw [h₁ 599 (by norm_num)]
    norm_num

  have h105 : f 604 = f (f 609) := by 
    rw [h₁ 604 (by norm_num)]
    norm_num

  have h106 : f 609 = f (f 614) := by 
    rw [h₁ 609 (by norm_num)]
    norm_num

  have h107 : f 614 = f (f 619) := by 
    rw [h₁ 614 (by norm_num)]
    norm_num

  have h108 : f 619 = f (f 624) := by 
    rw [h₁ 619 (by norm_num)]
    norm_num

  have h109 : f 624 = f (f 629) := by 
    rw [h₁ 624 (by norm_num)]
    norm_num

  have h110 : f 629 = f (f 634) := by 
    rw [h₁ 629 (by norm_num)]
    norm_num

  have h111 : f 634 = f (f 639) := by 
    rw [h₁ 634 (by norm_num)]
    norm_num

  have h112 : f 639 = f (f 644) := by 
    rw [h₁ 639 (by norm_num)]
    norm_num

  have h113 : f 644 = f (f 649) := by 
    rw [h₁ 644 (by norm_num)]
    norm_num

  have h114 : f 649 = f (f 654) := by 
    rw [h₁ 649 (by norm_num)]
    norm_num

  have h115 : f 654 = f (f 659) := by 
    rw [h₁ 654 (by norm_num)]
    norm_num

  have h116 : f 659 = f (f 664) := by 
    rw [h₁ 659 (by norm_num)]
    norm_num

  have h117 : f 664 = f (f 669) := by 
    rw [h₁ 664 (by norm_num)]
    norm_num

  have h118 : f 669 = f (f 674) := by 
    rw [h₁ 669 (by norm_num)]
    norm_num

  have h119 : f 674 = f (f 679) := by 
    rw [h₁ 674 (by norm_num)]
    norm_num

  have h120 : f 679 = f (f 684) := by 
    rw [h₁ 679 (by norm_num)]
    norm_num

  have h121 : f 684 = f (f 689) := by 
    rw [h₁ 684 (by norm_num)]
    norm_num

  have h122 : f 689 = f (f 694) := by 
    rw [h₁ 689 (by norm_num)]
    norm_num

  have h123 : f 694 = f (f 699) := by 
    rw [h₁ 694 (by norm_num)]
    norm_num

  have h124 : f 699 = f (f 704) := by 
    rw [h₁ 699 (by norm_num)]
    norm_num

  have h125 : f 704 = f (f 709) := by 
    rw [h₁ 704 (by norm_num)]
    norm_num

  have h126 : f 709 = f (f 714) := by 
    rw [h₁ 709 (by norm_num)]
    norm_num

  have h127 : f 714 = f (f 719) := by 
    rw [h₁ 714 (by norm_num)]
    norm_num

  have h128 : f 719 = f (f 724) := by 
    rw [h₁ 719 (by norm_num)]
    norm_num

  have h129 : f 724 = f (f 729) := by 
    rw [h₁ 724 (by norm_num)]
    norm_num

  have h130 : f 729 = f (f 734) := by 
    rw [h₁ 729 (by norm_num)]
    norm_num

  have h131 : f 734 = f (f 739) := by 
    rw [h₁ 734 (by norm_num)]
    norm_num

  have h132 : f 739 = f (f 744) := by 
    rw [h₁ 739 (by norm_num)]
    norm_num

  have h133 : f 744 = f (f 749) := by 
    rw [h₁ 744 (by norm_num)]
    norm_num

  have h134 : f 749 = f (f 754) := by 
    rw [h₁ 749 (by norm_num)]
    norm_num

  have h135 : f 754 = f (f 759) := by 
    rw [h₁ 754 (by norm_num)]
    norm_num

  have h136 : f 759 = f (f 764) := by 
    rw [h₁ 759 (by norm_num)]
    norm_num

  have h137 : f 764 = f (f 769) := by 
    rw [h₁ 764 (by norm_num)]
    norm_num

  have h138 : f 769 = f (f 774) := by 
    rw [h₁ 769 (by norm_num)]
    norm_num

  have h139 : f 774 = f (f 779) := by 
    rw [h₁ 774 (by norm_num)]
    norm_num

  have h140 : f 779 = f (f 784) := by 
    rw [h₁ 779 (by norm_num)]
    norm_num

  have h141 : f 784 = f (f 789) := by 
    rw [h₁ 784 (by norm_num)]
    norm_num

  have h142 : f 789 = f (f 794) := by 
    rw [h₁ 789 (by norm_num)]
    norm_num

  have h143 : f 794 = f (f 799) := by 
    rw [h₁ 794 (by norm_num)]
    norm_num

  have h144 : f 799 = f (f 804) := by 
    rw [h₁ 799 (by norm_num)]
    norm_num

  have h145 : f 804 = f (f 809) := by 
    rw [h₁ 804 (by norm_num)]
    norm_num

  have h146 : f 809 = f (f 814) := by 
    rw [h₁ 809 (by norm_num)]
    norm_num

  have h147 : f 814 = f (f 819) := by 
    rw [h₁ 814 (by norm_num)]
    norm_num

  have h148 : f 819 = f (f 824) := by 
    rw [h₁ 819 (by norm_num)]
    norm_num

  have h149 : f 824 = f (f 829) := by 
    rw [h₁ 824 (by norm_num)]
    norm_num

  have h150 : f 829 = f (f 834) := by 
    rw [h₁ 829 (by norm_num)]
    norm_num

  have h151 : f 834 = f (f 839) := by 
    rw [h₁ 834 (by norm_num)]
    norm_num

  have h152 : f 839 = f (f 844) := by 
    rw [h₁ 839 (by norm_num)]
    norm_num

  have h153 : f 844 = f (f 849) := by 
    rw [h₁ 844 (by norm_num)]
    norm_num

  have h154 : f 849 = f (f 854) := by 
    rw [h₁ 849 (by norm_num)]
    norm_num

  have h155 : f 854 = f (f 859) := by 
    rw [h₁ 854 (by norm_num)]
    norm_num

  have h156 : f 859 = f (f 864) := by 
    rw [h₁ 859 (by norm_num)]
    norm_num

  have h157 : f 864 = f (f 869) := by 
    rw [h₁ 864 (by norm_num)]
    norm_num

  have h158 : f 869 = f (f 874) := by 
    rw [h₁ 869 (by norm_num)]
    norm_num

  have h159 : f 874 = f (f 879) := by 
    rw [h₁ 874 (by norm_num)]
    norm_num

  have h160 : f 879 = f (f 884) := by 
    rw [h₁ 879 (by norm_num)]
    norm_num

  have h161 : f 884 = f (f 889) := by 
    rw [h₁ 884 (by norm_num)]
    norm_num

  have h162 : f 889 = f (f 894) := by 
    rw [h₁ 889 (by norm_num)]
    norm_num

  have h163 : f 894 = f (f 899) := by 
    rw [h₁ 894 (by norm_num)]
    norm_num

  have h164 : f 899 = f (f 904) := by 
    rw [h₁ 899 (by norm_num)]
    norm_num

  have h165 : f 904 = f (f 909) := by 
    rw [h₁ 904 (by norm_num)]
    norm_num

  have h166 : f 909 = f (f 914) := by 
    rw [h₁ 909 (by norm_num)]
    norm_num

  have h167 : f 914 = f (f 919) := by 
    rw [h₁ 914 (by norm_num)]
    norm_num

  have h168 : f 919 = f (f 924) := by 
    rw [h₁ 919 (by norm_num)]
    norm_num

  have h169 : f 924 = f (f 929) := by 
    rw [h₁ 924 (by norm_num)]
    norm_num

  have h170 : f 929 = f (f 934) := by 
    rw [h₁ 929 (by norm_num)]
    norm_num

  have h171 : f 934 = f (f 939) := by 
    rw [h₁ 934 (by norm_num)]
    norm_num

  have h172 : f 939 = f (f 944) := by 
    rw [h₁ 939 (by norm_num)]
    norm_num

  have h173 : f 944 = f (f 949) := by 
    rw [h₁ 944 (by norm_num)]
    norm_num

  have h174 : f 949 = f (f 954) := by 
    rw [h₁ 949 (by norm_num)]
    norm_num

  have h175 : f 954 = f (f 959) := by 
    rw [h₁ 954 (by norm_num)]
    norm_num

  have h176 : f 959 = f (f 964) := by 
    rw [h₁ 959 (by norm_num)]
    norm_num

  have h177 : f 964 = f (f 969) := by 
    rw [h₁ 964 (by norm_num)]
    norm_num

  have h178 : f 969 = f (f 974) := by 
    rw [h₁ 969 (by norm_num)]
    norm_num

  have h179 : f 974 = f (f 979) := by 
    rw [h₁ 974 (by norm_num)]
    norm_num

  have h180 : f 979 = f (f 984) := by 
    rw [h₁ 979 (by norm_num)]
    norm_num

  have h181 : f 984 = f (f 989) := by 
    rw [h₁ 984 (by norm_num)]
    norm_num

  have h182 : f 989 = f (f 994) := by 
    rw [h₁ 989 (by norm_num)]
    norm_num

  have h183 : f 994 = f (f 999) := by 
    rw [h₁ 994 (by norm_num)]
    norm_num

  have h184 : f 999 = f (f 1004) := by 
    rw [h₁ 999 (by norm_num)]
    norm_num

  have h185 : f 1004 = 1001 := by 
    rw [h₀ 1004 (by norm_num)]
    norm_num

  rw [h185] at h184
  have h186 : f 1001 = 998 := by 
    rw [h₀ 1001 (by norm_num)]
    norm_num

  rw [h186] at h184
  rw [h184] at h183
  
  rw [h183] at h182
  rw [h998] at h182

  rw [h182] at h181
  rw [h997] at h181

  rw [h181] at h180
  rw [h998] at h180

  rw [h180] at h179
  rw [h997] at h179

  rw [h179] at h178
  rw [h998] at h178

  rw [h178] at h177
  rw [h997] at h177

  rw [h177] at h176
  rw [h998] at h176

  rw [h176] at h175
  rw [h997] at h175

  rw [h175] at h174
  rw [h998] at h174

  rw [h174] at h173
  rw [h997] at h173

  rw [h173] at h172
  rw [h998] at h172

  rw [h172] at h171
  rw [h997] at h171

  rw [h171] at h170
  rw [h998] at h170

  rw [h170] at h169
  rw [h997] at h169

  rw [h169] at h168
  rw [h998] at h168

  rw [h168] at h167
  rw [h997] at h167

  rw [h167] at h166
  rw [h998] at h166

  rw [h166] at h165
  rw [h997] at h165

  rw [h165] at h164
  rw [h998] at h164

  rw [h164] at h163
  rw [h997] at h163

  rw [h163] at h162
  rw [h998] at h162

  rw [h162] at h161
  rw [h997] at h161

  rw [h161] at h160
  rw [h998] at h160

  rw [h160] at h159
  rw [h997] at h159

  rw [h159] at h158
  rw [h998] at h158

  rw [h158] at h157
  rw [h997] at h157

  rw [h157] at h156
  rw [h998] at h156

  rw [h156] at h155
  rw [h997] at h155

  rw [h155] at h154
  rw [h998] at h154

  rw [h154] at h153
  rw [h997] at h153

  rw [h153] at h152
  rw [h998] at h152

  rw [h152] at h151
  rw [h997] at h151

  rw [h151] at h150
  rw [h998] at h150

  rw [h150] at h149
  rw [h997] at h149

  rw [h149] at h148
  rw [h998] at h148

  rw [h148] at h147
  rw [h997] at h147

  rw [h147] at h146
  rw [h998] at h146

  rw [h146] at h145
  rw [h997] at h145

  rw [h145] at h144
  rw [h998] at h144

  rw [h144] at h143
  rw [h997] at h143

  rw [h143] at h142
  rw [h998] at h142

  rw [h142] at h141
  rw [h997] at h141

  rw [h141] at h140
  rw [h998] at h140

  rw [h140] at h139
  rw [h997] at h139

  rw [h139] at h138
  rw [h998] at h138

  rw [h138] at h137
  rw [h997] at h137

  rw [h137] at h136
  rw [h998] at h136

  rw [h136] at h135
  rw [h997] at h135

  rw [h135] at h134
  rw [h998] at h134

  rw [h134] at h133
  rw [h997] at h133

  rw [h133] at h132
  rw [h998] at h132

  rw [h132] at h131
  rw [h997] at h131

  rw [h131] at h130
  rw [h998] at h130

  rw [h130] at h129
  rw [h997] at h129

  rw [h129] at h128
  rw [h998] at h128

  rw [h128] at h127
  rw [h997] at h127

  rw [h127] at h126
  rw [h998] at h126

  rw [h126] at h125
  rw [h997] at h125

  rw [h125] at h124
  rw [h998] at h124

  rw [h124] at h123
  rw [h997] at h123

  rw [h123] at h122
  rw [h998] at h122

  rw [h122] at h121
  rw [h997] at h121

  rw [h121] at h120
  rw [h998] at h120

  rw [h120] at h119
  rw [h997] at h119

  rw [h119] at h118
  rw [h998] at h118

  rw [h118] at h117
  rw [h997] at h117

  rw [h117] at h116
  rw [h998] at h116

  rw [h116] at h115
  rw [h997] at h115

  rw [h115] at h114
  rw [h998] at h114

  rw [h114] at h113
  rw [h997] at h113

  rw [h113] at h112
  rw [h998] at h112

  rw [h112] at h111
  rw [h997] at h111

  rw [h111] at h110
  rw [h998] at h110

  rw [h110] at h109
  rw [h997] at h109

  rw [h109] at h108
  rw [h998] at h108

  rw [h108] at h107
  rw [h997] at h107

  rw [h107] at h106
  rw [h998] at h106

  rw [h106] at h105
  rw [h997] at h105

  rw [h105] at h104
  rw [h998] at h104

  rw [h104] at h103
  rw [h997] at h103

  rw [h103] at h102
  rw [h998] at h102

  rw [h102] at h101
  rw [h997] at h101

  rw [h101] at h100
  rw [h998] at h100

  rw [h100] at h99
  rw [h997] at h99

  rw [h99] at h98
  rw [h998] at h98

  rw [h98] at h97
  rw [h997] at h97

  rw [h97] at h96
  rw [h998] at h96

  rw [h96] at h95
  rw [h997] at h95

  rw [h95] at h94
  rw [h998] at h94

  rw [h94] at h93
  rw [h997] at h93

  rw [h93] at h92
  rw [h998] at h92

  rw [h92] at h91
  rw [h997] at h91

  rw [h91] at h90
  rw [h998] at h90

  rw [h90] at h89
  rw [h997] at h89

  rw [h89] at h88
  rw [h998] at h88

  rw [h88] at h87
  rw [h997] at h87

  rw [h87] at h86
  rw [h998] at h86

  rw [h86] at h85
  rw [h997] at h85

  rw [h85] at h84
  rw [h998] at h84

  rw [h84] at h83
  rw [h997] at h83

  rw [h83] at h82
  rw [h998] at h82

  rw [h82] at h81
  rw [h997] at h81

  rw [h81] at h80
  rw [h998] at h80

  rw [h80] at h79
  rw [h997] at h79

  rw [h79] at h78
  rw [h998] at h78

  rw [h78] at h77
  rw [h997] at h77

  rw [h77] at h76
  rw [h998] at h76

  rw [h76] at h75
  rw [h997] at h75

  rw [h75] at h74
  rw [h998] at h74

  rw [h74] at h73
  rw [h997] at h73

  rw [h73] at h72
  rw [h998] at h72

  rw [h72] at h71
  rw [h997] at h71

  rw [h71] at h70
  rw [h998] at h70

  rw [h70] at h69
  rw [h997] at h69

  rw [h69] at h68
  rw [h998] at h68

  rw [h68] at h67
  rw [h997] at h67

  rw [h67] at h66
  rw [h998] at h66

  rw [h66] at h65
  rw [h997] at h65

  rw [h65] at h64
  rw [h998] at h64

  rw [h64] at h63
  rw [h997] at h63

  rw [h63] at h62
  rw [h998] at h62

  rw [h62] at h61
  rw [h997] at h61

  rw [h61] at h60
  rw [h998] at h60

  rw [h60] at h59
  rw [h997] at h59

  rw [h59] at h58
  rw [h998] at h58

  rw [h58] at h57
  rw [h997] at h57

  rw [h57] at h56
  rw [h998] at h56

  rw [h56] at h55
  rw [h997] at h55

  rw [h55] at h54
  rw [h998] at h54

  rw [h54] at h53
  rw [h997] at h53

  rw [h53] at h52
  rw [h998] at h52

  rw [h52] at h51
  rw [h997] at h51

  rw [h51] at h50
  rw [h998] at h50

  rw [h50] at h49
  rw [h997] at h49

  rw [h49] at h48
  rw [h998] at h48

  rw [h48] at h47
  rw [h997] at h47

  rw [h47] at h46
  rw [h998] at h46

  rw [h46] at h45
  rw [h997] at h45

  rw [h45] at h44
  rw [h998] at h44

  rw [h44] at h43
  rw [h997] at h43

  rw [h43] at h42
  rw [h998] at h42

  rw [h42] at h41
  rw [h997] at h41

  rw [h41] at h40
  rw [h998] at h40

  rw [h40] at h39
  rw [h997] at h39

  rw [h39] at h38
  rw [h998] at h38

  rw [h38] at h37
  rw [h997] at h37

  rw [h37] at h36
  rw [h998] at h36

  rw [h36] at h35
  rw [h997] at h35

  rw [h35] at h34
  rw [h998] at h34

  rw [h34] at h33
  rw [h997] at h33

  rw [h33] at h32
  rw [h998] at h32

  rw [h32] at h31
  rw [h997] at h31

  rw [h31] at h30
  rw [h998] at h30

  rw [h30] at h29
  rw [h997] at h29

  rw [h29] at h28
  rw [h998] at h28

  rw [h28] at h27
  rw [h997] at h27

  rw [h27] at h26
  rw [h998] at h26

  rw [h26] at h25
  rw [h997] at h25

  rw [h25] at h24
  rw [h998] at h24

  rw [h24] at h23
  rw [h997] at h23

  rw [h23] at h22
  rw [h998] at h22

  rw [h22] at h21
  rw [h997] at h21

  rw [h21] at h20
  rw [h998] at h20

  rw [h20] at h19
  rw [h997] at h19

  rw [h19] at h18
  rw [h998] at h18

  rw [h18] at h17
  rw [h997] at h17

  rw [h17] at h16
  rw [h998] at h16

  rw [h16] at h15
  rw [h997] at h15

  rw [h15] at h14
  rw [h998] at h14

  rw [h14] at h13
  rw [h997] at h13

  rw [h13] at h12
  rw [h998] at h12

  rw [h12] at h11
  rw [h997] at h11

  rw [h11] at h10
  rw [h998] at h10

  rw [h10] at h9
  rw [h997] at h9

  rw [h9] at h8
  rw [h998] at h8

  rw [h8] at h7
  rw [h997] at h7

  rw [h7] at h6
  rw [h998] at h6

  rw [h6] at h5
  rw [h997] at h5

  rw [h5] at h4
  rw [h998] at h4

  rw [h4] at h3
  rw [h997] at h3

  rw [h3] at h2
  rw [h998] at h2

  rw [h2] at h1
  rw [h997] at h1

  linarith