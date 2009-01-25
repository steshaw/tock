//Note that in the occam 2 manual, there is an error on page 104.
//They say that range is the number of storable values in INTEGER,
//their conceptual infinite type, so range would be infinity!
//However, it is clear from the following lines that range is
//the number of storable values in INT.

#define occam_unsign(x) ((UINT)(x))
#define occam_sign(x) ((INT)(x))

static inline INT occam_LONGADD (INT, INT, INT, const char *) occam_unused;
static inline INT occam_LONGADD (INT left, INT right, INT carry_in, const char *pos) {
	if (left == __MAX(INT)) {
		if (right == __MAX(INT)) {
			occam_stop(pos, 3, "Overflow in LONGADD: %d + %d", left, right);
		} else right += carry_in & 1;
	} else left += carry_in & 1;

	if (((right<1)&&(__MIN(INT)-right<=left)) || ((right>=1)&&(__MAX(INT)-right>=left))) {
		return left + right;
	} else {
		occam_stop(pos, 3, "Overflow in LONGADD: %d + %d", left, right);
	}
}

static inline INT occam_LONGSUM (INT, INT, INT, INT*, const char *) occam_unused;
static inline INT occam_LONGSUM (INT left, INT right, INT carry_in, INT* result1, const char *pos) {
	UINT leftu = occam_unsign(left);
	UINT rightu = occam_unsign(right);
	if (leftu == __MAX(UINT)) {
		if (rightu == __MAX(UINT)) {
			*result1 = -2;
			return 1;
		} else rightu += carry_in & 1;
	} else leftu += carry_in & 1;

	if (__MAX(UINT)-rightu>=leftu) {
		*result1 = occam_sign(leftu + rightu);
		return 0;
	} else {
		*result1 = occam_sign(leftu + rightu);
		return 1;
	}
}

static inline INT occam_NORMALISE (INT, INT, INT*, INT*,const char *) occam_unused;
static inline INT occam_NORMALISE (INT hi_in, INT lo_in, INT* result1, INT* result2, const char *pos) {
	if (hi_in == 0 && lo_in == 0) {
		*result1 = *result2 = 0;
		return 2*CHAR_BIT*sizeof(INT);
	} else {
		const INT highest_bit = __MIN(INT);
		INT hi = hi_in;
		INT lo = lo_in;
		INT places = 0;
		while ((hi & highest_bit) == 0) {
			hi <<= 1;
			hi |= (lo & highest_bit) >> ((CHAR_BIT*sizeof(INT))-1);
			lo <<= 1;
			places++;
		}
		*result1 = hi;
		*result2 = lo;
		return places;
	}
}

////////////////////
//TODO implement, and move into the correct order above:
///////////////////

static inline INT occam_LONGSUB (INT, INT, const char *) occam_unused;
static inline INT occam_LONGSUB (INT left, INT right, INT borrow_in, const char *pos) {
	return 0;
}

static inline INT occam_LONGDIFF (INT, INT, INT, INT*, const char *) occam_unused;
static inline INT occam_LONGDIFF (INT left, INT right, INT borrow_in, INT* result1, const char *pos) {
	return 0;
}

static inline INT occam_LONGPROD (INT, INT, INT, INT*, const char *) occam_unused;
static inline INT occam_LONGPROD (INT left, INT right, INT carry_in, INT* result1, const char *pos) {
	return 0;
}

static inline INT occam_LONGDIV (INT, INT, INT, INT*, const char *) occam_unused;
static inline INT occam_LONGDIV (INT dividend_hi, INT dividend_lo, INT divisor, INT* result1, const char *pos) {
	return 0;
}

static inline INT occam_SHIFTRIGHT (INT, INT, INT, INT*, const char *) occam_unused;
static inline INT occam_SHIFTRIGHT (INT hi_in, INT lo_in, INT places, INT* result1, const char *pos) {
	return 0;
}

static inline INT occam_SHIFTLEFT (INT, INT, INT, INT*, const char *) occam_unused;
static inline INT occam_SHIFTLEFT (INT hi_in, INT lo_in, INT places, INT* result1, const char *pos) {
	return 0;
}

static inline INT occam_ASHIFTRIGHT (INT, INT, const char *) occam_unused;
static inline INT occam_ASHIFTRIGHT (INT x, INT places, const char *pos) {
	return 0;
}

static inline INT occam_ASHIFTLEFT (INT, INT, const char *) occam_unused;
static inline INT occam_ASHIFTLEFT (INT x, INT places, const char *pos) {
	return 0;
}

static inline INT occam_ROTATERIGHT (INT, INT, const char *) occam_unused;
static inline INT occam_ROTATERIGHT (INT x, INT places, const char *pos) {
	return (INT)((UINT)x >> places) | (x << (CHAR_BIT*sizeof(INT) - places));
}

static inline INT occam_ROTATELEFT (INT, INT, const char *) occam_unused;
static inline INT occam_ROTATELEFT (INT x, INT places, const char *pos) {
	return (x << places) | (INT)((UINT)x >> (CHAR_BIT*sizeof(INT) - places));
}


