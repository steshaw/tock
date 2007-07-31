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
#include <boost/any.hpp>
#include <vector>
#include <boost/type_traits/remove_const.hpp>
#include <boost/preprocessor/repetition/repeat.hpp>
#include <boost/preprocessor/repetition/repeat_from_to.hpp>

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


class tockBool
{
private: 
	bool b;
public: 
	inline tockBool() {}
	inline tockBool(bool _b) : b(_b) {}
	inline operator bool () const {return b;}
	inline void operator = (const bool& _b) {b = _b;}
};

inline std::pair< boost::array<unsigned,1> , unsigned > tockDims(const unsigned d0)
{
	boost::array<unsigned,1> r;
	r[0] = d0;
	return std::pair< boost::array<unsigned,1> , unsigned >(r,d0 == 0 ? 0 : 1);
}

/*
Generates functions like this:
inline std::pair< boost::array<unsigned,2> , unsigned > tockDims(const unsigned d0,const unsigned d1,const unsigned d2)
{
	boost::array<unsigned,2> r;
	r[0] = d0;
	r[1] = d1;
	r[2] = d2;
	return std::pair< boost::array<unsigned,2> , unsigned >(r,d1 * d2);
}
*/

#define TOCKDIMS_ARGS(___z,NUM,___data) ,const unsigned d##NUM
#define TOCKDIMS_ASSIGN(___z,NUM,___data) r[ NUM ] = d##NUM ;
#define TOCKDIMS_MULT(___z,NUM,___data) * d##NUM

#define TOCKDIMS(___z,NUM,___data) inline std::pair< boost::array<unsigned, NUM >,unsigned> tockDims(\
	const unsigned d0 BOOST_PP_REPEAT_FROM_TO(1,NUM,TOCKDIMS_ARGS,0) ) { \
	boost::array<unsigned, NUM > r; BOOST_PP_REPEAT(NUM,TOCKDIMS_ASSIGN,0) \
	return std::pair< boost::array<unsigned, NUM > , unsigned >(r,1 BOOST_PP_REPEAT_FROM_TO(1,NUM,TOCKDIMS_MULT,0) ); }

//Up to 12 dimensions:
BOOST_PP_REPEAT_FROM_TO(2,12,TOCKDIMS,0)


template < typename T, unsigned DIMS >
class tockArrayView
{
	T* realArray;
	boost::array<unsigned,DIMS> dims;
	//dims[1] * dims[2] * dims[3] ...
	//If DIMS is 0 or 1, totalSubDim will be 1
	unsigned totalSubDim;
	
	template <typename U>
	inline void operator=(const U&) {}
	
	inline tockArrayView(T* _realArray,const boost::array<unsigned,DIMS+1>& _biggerDims,unsigned _totalSubDim)
		:	realArray(_realArray),totalSubDim(_totalSubDim)
	{
		memcpy(dims.c_array(),_biggerDims.data() + 1,sizeof(unsigned) * DIMS);
	}
	friend class tockArrayView<T,DIMS + 1>;

	inline void correctDimsRetype(const unsigned totalSourceBytes)
	{
		if (totalSubDim == 0)
		{
			//Can only happen if one of the dimensions is zero, i.e. unknown
			//We must find this dimension and calculate it:
		
			unsigned zeroDim;
			unsigned totalDim = 1;
			for (unsigned i = 0;i < DIMS;i++)
			{
				if (dims[i] == 0)
					zeroDim = i;
				else
					totalDim *= dims[i];				
			}
			//Set the size of the unknown dimension:
			dims[zeroDim] = (totalSourceBytes / totalDim) / sizeof(T);
			
			totalSubDim = (totalDim * dims[zeroDim]) / dims[0];
		}
	
	}

	
public:
	inline tockArrayView()
		:	realArray(NULL)
	{
		dims.assign(0);
		totalSubDim = 0;
	}	

	inline tockArrayView(const tockArrayView& v)
		:	realArray(v.realArray),
			dims(v.dims),
			totalSubDim(v.totalSubDim)
	{
	}
	

	inline tockArrayView(T* _realArray,const std::pair< boost::array<unsigned,DIMS> , unsigned >& _dims)	
		:	realArray(_realArray),dims(_dims.first),totalSubDim(_dims.second)
	{
	}
	
	inline tockArrayView(std::vector<typename boost::remove_const<T>::type>& _vec,const std::pair< boost::array<unsigned,DIMS> , unsigned >& _dims)	
		:	realArray(_vec.empty() ? NULL : &(_vec.at(0))),dims(_dims.first),totalSubDim(_dims.second)
	{
	}	
	
	//Retyping:
	
	template <typename U>
	inline tockArrayView(U* _realArray,const std::pair< boost::array<unsigned,DIMS> , unsigned >& _dims)	
		:	realArray(reinterpret_cast<T*>(_realArray)),dims(_dims.first),totalSubDim(_dims.second)
	{
		//Assume it's a single U item:
		correctDimsRetype(sizeof(U));
	}
	
	
	//Retyping, same number of dims:
	template <typename U,unsigned FROMDIMS>
	inline tockArrayView(const tockArrayView<U,FROMDIMS>& tav,const std::pair< boost::array<unsigned,DIMS> , unsigned >& _dims)
		:	realArray(reinterpret_cast<T*>(tav.data())),dims(_dims.first),totalSubDim(_dims.second)
	{
		correctDimsRetype(tav.size() * sizeof(U));
	}
	
	inline tockArrayView<T,DIMS - 1> operator[] (const unsigned index) const
	{
		return tockArrayView<T,DIMS - 1>(realArray + (totalSubDim * index),dims,DIMS <= 1 ? 1 : (totalSubDim / dims[1]));
	}
	
	inline tockArrayView<T,DIMS> sliceFor(const unsigned amount) const
	{
		return sliceFromFor(0,amount);
	}

	inline tockArrayView<T,DIMS> sliceFrom(const unsigned index) const
	{
		return sliceFromFor(index,dims[0] - index);
	}	
	
	inline tockArrayView<T,DIMS> sliceFromFor(const unsigned index,const unsigned amount) const
	{
		boost::array<unsigned,DIMS> sliceDims = dims;
		sliceDims[0] = amount;
	
		return tockArrayView<T,DIMS>(realArray + (totalSubDim * index),std::make_pair(sliceDims,totalSubDim));
	}
	
	inline T* data() const 
	{
		return realArray;
	}	
	
	inline const boost::array<unsigned,DIMS>& getDims() const
	{
		return dims;
	}
	
	inline unsigned getTotalSubDim() const
	{
		return totalSubDim;
	}
	
	inline unsigned size() const
	{
		return dims[0] * totalSubDim;
	}
	
	inline unsigned extent(const unsigned dim) const	
	{
		return dims[dim];
	}
	
	inline operator tockArrayView<const T,DIMS>() const
	{
		return tockArrayView<const T,DIMS>((const T*)realArray,std::make_pair(dims,totalSubDim));
	}
	
	inline void updateFromVector(std::vector<typename boost::remove_const<T>::type>& v)
	{
		realArray = v.empty() ? NULL : &(v.at(0));
	}
		
	inline tockArrayView<typename boost::remove_const<T>::type,DIMS> versionToSend()
	{
		return tockArrayView<typename boost::remove_const<T>::type,DIMS>(const_cast<typename boost::remove_const<T>::type*>(realArray),std::make_pair(dims,totalSubDim));
	}
	
	inline const tockArrayView<typename boost::remove_const<T>::type,DIMS> versionToSend() const
	{
		return tockArrayView<typename boost::remove_const<T>::type,DIMS>(const_cast<typename boost::remove_const<T>::type*>(realArray),std::make_pair(dims,totalSubDim));
	}	
	
	inline tockArrayView& operator=(const tockArrayView& tav)
	{
		//TODO investigate speeding up when T is primitive (maybe there's a boost class for that?)
		
		unsigned n = tav.size();
		for (unsigned i = 0;i < n;i++)
		{
			realArray[i] = tav.realArray[i];
		}
		
		dims = tav.dims;
		totalSubDim = tav.totalSubDim;
		return *this;
	}
	
	inline tockArrayView& operator=(const tockAny&)
	{
		//TODO later on
	}
};

template <typename T>
class tockArrayView<T,0>
{
	T* realArray;		
	
	inline tockArrayView(T* _realArray,boost::array<unsigned,1>,unsigned)
        :   realArray(_realArray)
    {
    }
    
    friend class tockArrayView<T,1>;
    
public:

	//Should only be used on arrays with zero dimensions:
	inline T& access() const
	{
		return *realArray;
	}
};
