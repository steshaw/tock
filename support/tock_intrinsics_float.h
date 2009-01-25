static inline INT ADD_PREFIX(IEEECOMPARE) (REAL, REAL, const char*) occam_unused;
static inline INT ADD_PREFIX(IEEECOMPARE) (REAL X, REAL Y, const char* pos) {
	if (isunordered(X,Y)) {
		return 2;
	} else if (isgreater(X,Y)) {
		return 1;
	} else if (isless(X,Y)) {
		return -1;
	} else {
		return 0;
	}
}
static inline BOOL SPLICE_SIZE(occam_IEEE,OP) (REAL, INT, INT, REAL, REAL*, const char*) occam_unused;
static inline BOOL SPLICE_SIZE(occam_IEEE,OP) (REAL X, INT Rm, INT Op, REAL Y, REAL* result1, const char* pos) {
	return 0;
}
static inline BOOL SPLICE_SIZE(occam_IEEE,REM) (REAL, REAL, REAL*, const char*) occam_unused;
static inline BOOL SPLICE_SIZE(occam_IEEE,REM) (REAL X, REAL Y, REAL* result1, const char* pos) {
	return 0;
}
static inline BOOL SPLICE_SIZE(occam_REAL,EQ) (REAL, REAL, const char*) occam_unused;
static inline BOOL SPLICE_SIZE(occam_REAL,EQ) (REAL X, REAL Y, const char* pos) {
	return 0;
}
static inline BOOL SPLICE_SIZE(occam_REAL,GT) (REAL, REAL, const char*) occam_unused;
static inline BOOL SPLICE_SIZE(occam_REAL,GT) (REAL X, REAL Y, const char* pos) {
	return isgreater(X,Y);
}
static inline REAL SPLICE_SIZE(occam_REAL,OP) (REAL, INT, REAL, const char*) occam_unused;
static inline REAL SPLICE_SIZE(occam_REAL,OP) (REAL X, INT Op, REAL Y, const char* pos) {
	return 0;
}
static inline REAL SPLICE_SIZE(occam_REAL,REM) (REAL, REAL, const char*) occam_unused;
static inline REAL SPLICE_SIZE(occam_REAL,REM) (REAL X, REAL Y, const char* pos) {
	return 0;
}
#if SPLICE_SIZE(4,1) == 4321
static inline BOOL occam_ARGUMENT_REDUCE (float, float, float, int32_t*, float*, const char*) occam_unused;
static inline BOOL occam_ARGUMENT_REDUCE (float X, float Y, float Y_err, int32_t* result1, float* result2, const char* pos) {
	return 0;
}
#else
static inline BOOL occam_DARGUMENT_REDUCE (double, double, double, int32_t*, double*, const char*) occam_unused;
static inline BOOL occam_DARGUMENT_REDUCE (double X, double Y, double Y_err, int32_t* result1, double* result2, const char* pos) {
	return 0;
}
#endif
static inline REAL ADD_PREFIX(ABS) (REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(ABS) (REAL X, const char* pos) {
	return 0;
}
static inline REAL ADD_PREFIX(COPYSIGN) (REAL, REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(COPYSIGN) (REAL X, REAL Y, const char* pos) {
	return F(copysign)(X,Y);
}
static inline REAL ADD_PREFIX(DIVBY2) (REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(DIVBY2) (REAL X, const char* pos) {
	return 0;
}
static inline INT ADD_PREFIX(FLOATING_UNPACK) (REAL, REAL*, const char*) occam_unused;
static inline INT ADD_PREFIX(FLOATING_UNPACK) (REAL X, REAL* result1, const char* pos) {
	return 0;
}
static inline REAL ADD_PREFIX(FPINT) (REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(FPINT) (REAL X, const char* pos) {
	return 0;
}
static inline BOOL ADD_PREFIX(ISNAN) (REAL, const char*) occam_unused;
static inline BOOL ADD_PREFIX(ISNAN) (REAL X, const char* pos) {
	return 0;
}
static inline REAL ADD_PREFIX(LOGB) (REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(LOGB) (REAL X, const char* pos) {
	return 0;
}
static inline REAL ADD_PREFIX(MINUSX) (REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(MINUSX) (REAL X, const char* pos) {
	return 0;
}
static inline REAL ADD_PREFIX(MULBY2) (REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(MULBY2) (REAL X, const char* pos) {
	return 0;
}
static inline REAL ADD_PREFIX(NEXTAFTER) (REAL, REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(NEXTAFTER) (REAL X, REAL Y, const char* pos) {
	return 0;
}
static inline BOOL ADD_PREFIX(NOTFINITE) (REAL, const char*) occam_unused;
static inline BOOL ADD_PREFIX(NOTFINITE) (REAL X, const char* pos) {
	return 0;
}
static inline BOOL ADD_PREFIX(ORDERED) (REAL, REAL, const char*) occam_unused;
static inline BOOL ADD_PREFIX(ORDERED) (REAL X, REAL Y, const char* pos) {
	return !(isunordered(X,Y));
}
static inline REAL ADD_PREFIX(SCALEB) (REAL, INT, const char*) occam_unused;
static inline REAL ADD_PREFIX(SCALEB) (REAL X, INT n, const char* pos) {
	return 0;
}
static inline REAL ADD_PREFIX(SQRT) (REAL, const char*) occam_unused;
static inline REAL ADD_PREFIX(SQRT) (REAL X, const char* pos) {
	return F(sqrt)(X);
}

