//Note that in the occam 2 manual, there is an error on page 104.
//They say that range is the number of storable values in INTEGER,
//their conceptual infinite type, so range would be infinity!
//However, it is clear from the following lines that range is
//the number of storable values in INT.

#define occam_unsign(x) ((OCCAM_UINT)(x))
#define occam_sign(x) ((OCCAM_INT)(x))

static inline OCCAM_INT occam_LONGADD (OCCAM_INT, OCCAM_INT, OCCAM_INT, const char *) occam_unused;
static inline OCCAM_INT occam_LONGADD (OCCAM_INT left, OCCAM_INT right, OCCAM_INT carry_in, const char *pos) {
	if (left == __MAX(OCCAM_INT)) {
		if (right == __MAX(OCCAM_INT)) {
			occam_stop(pos, 3, "Overflow in LONGADD: %d + %d", left, right);
		} else right += carry_in & 1;
	} else left += carry_in & 1;

	if (((right<1)&&(__MIN(OCCAM_INT)-right<=left)) || ((right>=1)&&(__MAX(OCCAM_INT)-right>=left))) {
		return left + right;
	} else {
		occam_stop(pos, 3, "Overflow in LONGADD: %d + %d", left, right);
	}
}

static inline OCCAM_INT occam_LONGDIFF (OCCAM_INT, OCCAM_INT, OCCAM_INT, OCCAM_INT*, const char *) occam_unused;
static inline OCCAM_INT occam_LONGDIFF (OCCAM_INT left, OCCAM_INT right, OCCAM_INT borrow_in, OCCAM_INT* result1, const char *pos) {
	OCCAM_UINT leftu = occam_unsign(left);
	OCCAM_UINT rightu = occam_unsign(right);
	if (leftu == 0) {
		if (rightu == __MAX(OCCAM_UINT)) {
			*result1 = 1 - (borrow_in & 1);
			return 1;
		} else rightu += borrow_in & 1;
	} else leftu -= borrow_in & 1;
	
	if (rightu > leftu) {
		//This will overflow -- could be a problem on odd C implementations		
		*result1 = occam_sign(leftu - rightu);
		return 1;
	} else {
		*result1 = occam_sign(leftu - rightu);
		return 0;
	}
}

static inline OCCAM_INT occam_LONGPROD (OCCAM_INT, OCCAM_INT, OCCAM_INT, OCCAM_INT*, const char *) occam_unused;
static inline OCCAM_INT occam_LONGPROD (OCCAM_INT left, OCCAM_INT right, OCCAM_INT carry_in, OCCAM_INT* result1, const char *pos) {
	const OCCAM_UINT leftu = occam_unsign(left);
	const OCCAM_UINT rightu = occam_unsign(right);
	const OCCAM_UINT carryu = occam_unsign(carry_in);
#define HI_HALF(x) (x >> (CHAR_BIT*sizeof(OCCAM_INT)/2))
#define LO_HALF(x) (x & ((1<<(CHAR_BIT*sizeof(OCCAM_INT)/2))-1))
#define MAKE_HI(x) (x << (CHAR_BIT*sizeof(OCCAM_INT)/2))
	const OCCAM_UINT leftu_hi = HI_HALF(leftu);
	const OCCAM_UINT rightu_hi = HI_HALF(rightu);
	const OCCAM_UINT leftu_lo = LO_HALF(leftu);
	const OCCAM_UINT rightu_lo = LO_HALF(rightu);

	OCCAM_UINT prod_lo = leftu_lo * rightu_lo;
	OCCAM_UINT prod_hi = leftu_hi * rightu_hi;
	const OCCAM_UINT prod_med0 = leftu_lo * rightu_hi;
	const OCCAM_UINT prod_med1 = leftu_hi * rightu_lo;
	//E.g.s given for 8-bit, L=15,M=255:
	//prod_hi has max value 225 (L*L)
	//HI_HALF(prod_med0|1) has max value 14 (L*L)/(L+1)
	//So no overflow possible here:
	prod_hi += HI_HALF(prod_med0) + HI_HALF(prod_med1);
	//prod_hi cannot overflow from these carries,
	//As mathematically, (M*M)+M < ((M+1)*(M+1)) - 1
	
	prod_hi += (__MAX(OCCAM_UINT) - prod_lo >= MAKE_HI(LO_HALF(prod_med0))) ? 0 : 1;
	prod_lo += MAKE_HI(LO_HALF(prod_med0));

	prod_hi += (__MAX(OCCAM_UINT) - prod_lo >= MAKE_HI(LO_HALF(prod_med1))) ? 0 : 1;
	prod_lo += MAKE_HI(LO_HALF(prod_med1));

	prod_hi += (__MAX(OCCAM_UINT) - prod_lo >= carryu) ? 0 : 1;
	prod_lo += carryu;
	
	*result1 = occam_sign(prod_lo);
	return prod_hi;
#undef HI_HALF
#undef LO_HALF
#undef MAKE_HI
}

static inline OCCAM_INT occam_LONGSUB (OCCAM_INT, OCCAM_INT, OCCAM_INT, const char *) occam_unused;
static inline OCCAM_INT occam_LONGSUB (OCCAM_INT left, OCCAM_INT right, OCCAM_INT borrow_in, const char *pos) {
	if (left == __MIN(OCCAM_INT)) {
		if (right == __MIN(OCCAM_INT)) {
			occam_stop(pos, 3, "Overflow in LONGSUB: %d - %d", left, right);
		} else right -= borrow_in & 1;
	} else left -= borrow_in & 1;

	if (((right<1)&&(__MAX(OCCAM_INT)+right>=left)) || ((right>=1)&&(__MIN(OCCAM_INT)+right<=left))) {
		return left - right;
	} else {
		occam_stop(pos, 3, "Overflow in LONGSUB: %d - %d", left, right);
	}
}

static inline OCCAM_INT occam_LONGSUM (OCCAM_INT, OCCAM_INT, OCCAM_INT, OCCAM_INT*, const char *) occam_unused;
static inline OCCAM_INT occam_LONGSUM (OCCAM_INT left, OCCAM_INT right, OCCAM_INT carry_in, OCCAM_INT* result1, const char *pos) {
	OCCAM_UINT leftu = occam_unsign(left);
	OCCAM_UINT rightu = occam_unsign(right);
	if (leftu == __MAX(OCCAM_UINT)) {
		if (rightu == __MAX(OCCAM_UINT)) {
			*result1 = -2 + (carry_in & 1);
			return 1;
		} else rightu += carry_in & 1;
	} else leftu += carry_in & 1;

	if (__MAX(OCCAM_UINT)-rightu>=leftu) {
		*result1 = occam_sign(leftu + rightu);
		return 0;
	} else {
		//This will overflow -- could be a problem on odd C implementations
		*result1 = occam_sign(leftu + rightu);
		return 1;
	}
}

static inline OCCAM_INT occam_NORMALISE (OCCAM_INT, OCCAM_INT, OCCAM_INT*, OCCAM_INT*,const char *) occam_unused;
static inline OCCAM_INT occam_NORMALISE (OCCAM_INT hi_in, OCCAM_INT lo_in, OCCAM_INT* result1, OCCAM_INT* result2, const char *pos) {
	if (hi_in == 0 && lo_in == 0) {
		*result1 = *result2 = 0;
		return 2*CHAR_BIT*sizeof(OCCAM_INT);
	} else {
		const OCCAM_INT highest_bit = __MIN(OCCAM_INT);
		OCCAM_INT hi = hi_in;
		OCCAM_INT lo = lo_in;
		OCCAM_INT places = 0;
		while ((hi & highest_bit) == 0) {
			hi <<= 1;
			hi |= (lo & highest_bit) >> ((CHAR_BIT*sizeof(OCCAM_INT))-1);
			lo <<= 1;
			places++;
		}
		*result1 = hi;
		*result2 = lo;
		return places;
	}
}

//Has to go late on due to its function re-use:

static inline OCCAM_INT occam_LONGDIV (OCCAM_INT, OCCAM_INT, OCCAM_INT, OCCAM_INT*, const char *) occam_unused;
static inline OCCAM_INT occam_LONGDIV (OCCAM_INT dividend_hi, OCCAM_INT dividend_lo, OCCAM_INT divisor, OCCAM_INT* result1, const char *pos) {
	OCCAM_UINT top_hi = occam_unsign(dividend_hi);
	OCCAM_UINT top_lo = occam_unsign(dividend_lo);
	const OCCAM_UINT bottom = occam_unsign(divisor);
	
	//Intuititively, the algorithm works as follows:
	//We work out how many Hi there are remaining in the
	//Hi part after the Hi/Bot division.  We then have
	//Hi%Bot loads of R left.  We can immediately
	//add Hi%Bot * R/bot to the result, leaving
	// Hi%Bot * R%Bot left.  We must (long-)add this
	//quantity to Lo, and repeat the procedure, until
	// Hi is zero.
	
	if (bottom == 0) {
		occam_stop(pos, 1, "Division by zero in LONGDIV");
	} else {
		OCCAM_UINT r_hi = 0;
		OCCAM_UINT r_lo = 0;

		OCCAM_UINT amount_extra_R_over_bot = 0;
		
		//We can work R/bot out by doing:
		// (R/2)/bot + ((R/2)%bot + (R/2)/bot
		const OCCAM_UINT halfR = occam_unsign(__MIN(OCCAM_INT));
		OCCAM_UINT R_over_bot = bottom >= halfR ? 1 : (halfR/bottom + ((halfR % bottom) + halfR) / bottom);
		OCCAM_UINT R_mod_bot = (__MAX(OCCAM_UINT)%bottom) == bottom - 1 ? 0 : 1+(__MAX(OCCAM_UINT)%bottom);

		while (top_hi != 0) {
			r_hi += top_hi / bottom;
			r_lo += top_lo / bottom;
			top_lo %= bottom;
			top_hi %= bottom;
			amount_extra_R_over_bot += top_hi;
			top_hi = occam_unsign(occam_LONGPROD(occam_sign(top_hi),occam_sign(R_mod_bot),occam_sign(top_lo),(OCCAM_INT*)&top_lo,pos));
		}

		//long-add the results from top_lo/bottom to r_hi,r_lo:
		r_hi += occam_unsign(occam_LONGSUM(occam_sign(r_lo),occam_sign(top_lo/bottom),0,(OCCAM_INT*)&r_lo,pos));
		//Save the remainder for later:
		const OCCAM_UINT rem = top_lo%bottom;
		
		//Finally, add on R_over_bot * amount_extra_R_over_bot
		top_hi = occam_unsign(occam_LONGPROD(occam_sign(R_over_bot), occam_sign(amount_extra_R_over_bot), 0, (OCCAM_INT*)&top_lo,pos));
		r_hi += top_hi + occam_unsign(occam_LONGSUM(occam_sign(r_lo), occam_sign(top_lo), 0, (OCCAM_INT*)&r_lo, pos));
		
		if (r_hi == 0) {
			*result1 = occam_sign(rem);
			return occam_sign(r_lo);
		} else {
			occam_stop(pos,4,"Overflow in LONGDIV(%d,%d,%d)", dividend_hi, dividend_lo, divisor);
		}	
	}
}

static inline OCCAM_INT occam_SHIFTLEFT (OCCAM_INT, OCCAM_INT, OCCAM_INT, OCCAM_INT*, const char *) occam_unused;
static inline OCCAM_INT occam_SHIFTLEFT (OCCAM_INT hi_in, OCCAM_INT lo_in, OCCAM_INT places, OCCAM_INT* result1, const char *pos) {
	if (places >= (OCCAM_INT)(CHAR_BIT*sizeof(OCCAM_INT))) {
		*result1 = 0;
		return occam_sign(occam_unsign(lo_in) << (places - CHAR_BIT*sizeof(OCCAM_INT)));
	} else {
		const OCCAM_UINT r_lo = occam_unsign(lo_in) << places;
		const OCCAM_UINT r_hi = (occam_unsign(hi_in) << places) | (occam_unsign(lo_in) >> (CHAR_BIT*sizeof(OCCAM_INT)-places));
		*result1 = occam_sign(r_lo);
		return r_hi;
	}
}

static inline OCCAM_INT occam_SHIFTRIGHT (OCCAM_INT, OCCAM_INT, OCCAM_INT, OCCAM_INT*, const char *) occam_unused;
static inline OCCAM_INT occam_SHIFTRIGHT (OCCAM_INT hi_in, OCCAM_INT lo_in, OCCAM_INT places, OCCAM_INT* result1, const char *pos) {
	if (places >= (OCCAM_INT)(CHAR_BIT*sizeof(OCCAM_INT))) {
		*result1 = occam_sign(occam_unsign(hi_in) >> (places - CHAR_BIT*sizeof(OCCAM_INT)));
		return 0;
	} else {
		const OCCAM_UINT r_hi = occam_unsign(hi_in) >> places;
		const OCCAM_UINT r_lo = (occam_unsign(lo_in) >> places) | (occam_unsign(hi_in) << (CHAR_BIT*sizeof(OCCAM_INT)-places));
		*result1 = occam_sign(r_lo);
		return r_hi;
	}
}

static inline OCCAM_INT occam_ASHIFTRIGHT (OCCAM_INT, OCCAM_INT, const char *) occam_unused;
static inline OCCAM_INT occam_ASHIFTRIGHT (OCCAM_INT x, OCCAM_INT places, const char *pos) {
	return x >> places;
}

static inline OCCAM_INT occam_ASHIFTLEFT (OCCAM_INT, OCCAM_INT, const char *) occam_unused;
static inline OCCAM_INT occam_ASHIFTLEFT (OCCAM_INT x, OCCAM_INT places, const char *pos) {
	//Overflows if positive and 1 bits are shifted out or highest bit ends as 1,
	//or negative and 0 bits are shifted out or highest bit ends as 0
	if (places > (OCCAM_INT)(CHAR_BIT*sizeof(OCCAM_INT))
	    || places < 0
	    || (places == (OCCAM_INT)(CHAR_BIT*sizeof(OCCAM_INT)) && x != 0)) {
		occam_stop(pos,3,"Overflow in ASHIFTLEFT(%d,%d)",x,places);
	}
	else if (places != (OCCAM_INT)(CHAR_BIT*sizeof(OCCAM_INT)) && places != 0 &&
	      (occam_unsign(x) >> (CHAR_BIT*sizeof(OCCAM_INT)-places-1) != 
	       occam_unsign(x < 0 ? (OCCAM_INT)-1 : (OCCAM_INT)0) >> (CHAR_BIT*sizeof(OCCAM_INT)-places-1))) {
		occam_stop(pos,3,"Overflow in ASHIFTLEFT(%d,%d)",x,places);
	} else {
		return (x << places);
	}
}

static inline OCCAM_INT occam_ROTATERIGHT (OCCAM_INT, OCCAM_INT, const char *) occam_unused;
static inline OCCAM_INT occam_ROTATERIGHT (OCCAM_INT x, OCCAM_INT places, const char *pos) {
	return (OCCAM_INT)((OCCAM_UINT)x >> places) | (x << (CHAR_BIT*sizeof(OCCAM_INT) - places));
}

static inline OCCAM_INT occam_ROTATELEFT (OCCAM_INT, OCCAM_INT, const char *) occam_unused;
static inline OCCAM_INT occam_ROTATELEFT (OCCAM_INT x, OCCAM_INT places, const char *pos) {
	return (x << places) | (OCCAM_INT)((OCCAM_UINT)x >> (CHAR_BIT*sizeof(OCCAM_INT) - places));
}


