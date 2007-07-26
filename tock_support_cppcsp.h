//To get the UINT8_MAX etc macros in C++:
#define __STDC_LIMIT_MACROS

#include <string>

class StopException
{
public:
	std::string reason;
	inline StopException(const std::string& _reason)
		:	reason(_reason)
	{
	}
};

#define occam_stop(pos, format, args...) \
    do { \
        EXTERNAL_CALLN (fprintf, stderr, "Program stopped at %s: " format "\n", pos, ##args); \
        SetErr (); \
        throw StopException(""); \
    } while (0)

#define NO_CIFCCSP

#include "tock_support.h"

#include <cppcsp/cppcsp.h>
#include <cppcsp/common/basic.h>
#include <iostream>
#include <boost/tuple/tuple.hpp>
#include <boost/variant.hpp>
#include <boost/mpl/at.hpp>
#include <blitz/array.h>
#include <blitz/tinyvec-et.h>
#include <boost/any.hpp>

inline blitz::Array<unsigned char, 1> string_to_array(char* c)
{
	const size_t n = strlen(c) + 1;
	return blitz::Array<unsigned char, 1>((unsigned char*)c,blitz::shape(n),blitz::neverDeleteData);
}


class StreamWriter : public csp::CSProcess
{
private:
	std::ostream& out; 	
	csp::Chanin<uint8_t> in;
protected:
	virtual void run()
	{
		try
		{
			uint8_t c;
			while (true)
			{
				in >> c;
				out << c;
			}
			out.flush();
		}
		catch (csp::PoisonException& e)
		{
			in.poison();
		}
	}
public:
	inline StreamWriter(std::ostream& _out,const csp::Chanin<uint8_t>& _in)
		:	out(_out),in(_in)
	{
	}
};


//For tieing together chained tuples:

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7,
         class T8, class T9, class T10>
inline boost::tuple<T1&, T2&, T3&, T4&, T5&, T6&, T7&, T8&, T9&, T10>
tie10(T1& t1, T2& t2, T3& t3, T4& t4, T5& t5, T6& t6, T7& t7, T8& t8,
           T9& t9, T10 t10) {
  return boost::tuple<T1&, T2&, T3&, T4&, T5&, T6&, T7&, T8&, T9&, T10>
           (t1, t2, t3, t4, t5, t6, t7, t8, t9, t10);
}


class tockAny : public boost::any
{
public:
	inline tockAny() {}
	
	inline tockAny(const tockAny& t)
		:	boost::any(*(boost::any*)&t)
	{
	}

	template <typename T>
	inline tockAny(T t) : boost::any(t) {}
	
	template <typename T>
	inline operator T () const
	{
		return boost::any_cast<T>(*this);
	}
};


template < typename T, unsigned dims >
class tockArray : public blitz::Array<T,dims>
{
public:
	inline tockArray(const tockArray<T,dims>& _array)
		:	blitz::Array<T,dims>(*(blitz::Array<T,dims>*)&_array) {}

	inline tockArray(const tockAny& _any)
		:	blitz::Array<T,dims>(*(blitz::Array<T,dims>*)& (tockArray)_any) {}		

	template <typename U>
	inline tockArray(const tockArray<U,dims>& _diffTypeArray)
		:	blitz::Array<T,dims>( (T*) (_diffTypeArray.dataFirst()), (_diffTypeArray.shape() * (int)sizeof(U)) / (int)sizeof(T),blitz::neverDeleteData) {}

	template <unsigned D>
	inline tockArray(const tockArray<T,D>& _diffDimArray)
		:   blitz::Array<T,dims>( (T*) (_diffDimArray.dataFirst()),blitz::shape(_diffDimArray.size()),blitz::neverDeleteData) {}

	template <typename U>
	inline tockArray(U* u)
		:	blitz::Array<T,dims>( (T*) u, sizeof(U) / sizeof(T),blitz::neverDeleteData) {}

	inline tockArray(T t) : blitz::Array<T,dims>(1) {(*this)(0) = t;}


	template <typename U>
	inline tockArray(U u) : blitz::Array<T,dims>(u) {}

	template <typename U,typename V>
	inline tockArray(U u,V v) : blitz::Array<T,dims>(u,v) {}
	
	template <typename U,typename V,typename W>
	inline tockArray(U u,V v,W w) : blitz::Array<T,dims>(u,v,w) {}

	template <typename U,typename V,typename W,typename X>
	inline tockArray(U u,V v,W w,X x) : blitz::Array<T,dims>(u,v,w,x) {}

	template <typename U,typename V,typename W,typename X,typename Y>
	inline tockArray(U u,V v,W w,X x,Y y) : blitz::Array<T,dims>(u,v,w,x,y) {}	

	template <typename U,typename V,typename W,typename X,typename Y,typename Z>
	inline tockArray(U u,V v,W w,X x,Y y,Z z) : blitz::Array<T,dims>(u,v,w,x,y,z) {}
	
	template <typename U,typename V,typename W,typename X,typename Y,typename Z,typename Z0>
	inline tockArray(U u,V v,W w,X x,Y y,Z z,Z0 z0) : blitz::Array<T,dims>(u,v,w,x,y,z,z0) {}	

	template <typename U,typename V,typename W,typename X,typename Y,typename Z,typename Z0,typename Z1>
	inline tockArray(U u,V v,W w,X x,Y y,Z z,Z0 z0,Z1 z1) : blitz::Array<T,dims>(u,v,w,x,y,z,z0,z1) {}
	
	template <typename U,typename V,typename W,typename X,typename Y,typename Z,typename Z0,typename Z1,typename Z2>
	inline tockArray(U u,V v,W w,X x,Y y,Z z,Z0 z0,Z1 z1,Z2 z2) : blitz::Array<T,dims>(u,v,w,x,y,z,z0,z1,z2) {}	

	template <typename U,typename V,typename W,typename X,typename Y,typename Z,typename Z0,typename Z1,typename Z2,typename Z3>
	inline tockArray(U u,V v,W w,X x,Y y,Z z,Z0 z0,Z1 z1,Z2 z2,Z3 z3) : blitz::Array<T,dims>(u,v,w,x,y,z,z0,z1,z2,z3) {}		

	
	inline tockArray() {}
	
	inline tockArray& operator=(const tockArray<T,dims>& rhs)
	{
		resize(rhs.shape());
		*((blitz::Array<T,dims>*)this) = *((blitz::Array<T,dims>*)&rhs);
		return *this;
	}
	
	inline tockArray& operator=(const tockAny& any)
	{
		return (*this = (tockArray<T,dims>)any);
	}
	
	inline tockArray& operator=(const T& t)
	{
		this->resize(blitz::shape(1));
		(*this)(0) = t;
		return *this;
	}
	
	template <typename U>
	operator U* ()
	{
		return (U*)(void*)(this->dataFirst());
	}

	template <typename U>
	operator const U* const ()
	{
		return (const U*)(const void*)(this->dataFirst());
	}
	
};
