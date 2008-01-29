/*
 * C++ support code for Tock programs
 * Copyright (C) 2007  University of Kent
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library.  If not, see <http://www.gnu.org/licenses/>.
 */

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
#include <vector>
#include <list>
#include <boost/type_traits/remove_const.hpp>
#include <boost/preprocessor/repetition/repeat.hpp>
#include <boost/preprocessor/repetition/repeat_from_to.hpp>
#include <boost/tuple/tuple.hpp>

inline unsigned TimeDiffHelper(unsigned now,unsigned waitFor)
{
	//If waitFor is in the 2^31 before now, it is in the past:
	if (now - waitFor < 2147483648)
	{
		//if we have wrapped round between waitFor and now, we actually want to return a minus-one:
		if ((waitFor >= 2147483648) && (now < 2147483648))
		{
			return (unsigned)(int)(-1);
		}
		else
		{
			return 0;
		}
	}
	else
	{
		//It is in the future.  If we will wrap round before getting there, return one:
		if ((now >= 2147483648) && (waitFor < 2147483648))
		{
			return 1;
		}
		else
		{
			return 0;
		}
	}
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

	//TODO change the other methods so we can feed a string in here (the Meta) to report to occam_stop
	inline void correctDimsRetype(const unsigned totalSourceBytes)
	{
		if (totalSubDim == 0 || dims[0] == 0)
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
			
			//Check it fits exactly:
			if ((totalSourceBytes / totalDim) % sizeof(T) != 0)
			{
				occam_stop ("","invalid size for RETYPES/RESHAPES (%d does not divide into %d)", (totalSourceBytes / totalDim), sizeof(T));
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
	
	//The retyping constructors have their parameters in the other order to the same-type functions above,
	//to avoid ambiguities between retyping and same types (especially when const is involved):

	template <typename U>
	inline tockArrayView(const std::pair< boost::array<unsigned,DIMS> , unsigned >& _dims,U* _realArray)
		:	realArray(reinterpret_cast<T*>(_realArray)),dims(_dims.first),totalSubDim(_dims.second)
	{
		//Assume it's a single U item:
		correctDimsRetype(sizeof(U));
	}
	
	
	//Retyping, same number of dims:
	template <typename U,unsigned FROMDIMS>
	inline tockArrayView(const std::pair< boost::array<unsigned,DIMS> , unsigned >& _dims,const tockArrayView<U,FROMDIMS>& tav)
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

class tockSendableArrayOfBytes
{
private:
	unsigned n;
	///This is not as horrific as it looks - it is never used as a way to get rid of the const tag on the same pointer, only one field is used at a time.
	union
	{
		const void* sp;
		void* dp;
	};
public:
	///For the sender:
	inline explicit tockSendableArrayOfBytes(const void* p)
		:	n(0),sp(p)
	{
	}
	
	///Also for the sender:
	template <typename T, unsigned N>
	inline explicit tockSendableArrayOfBytes(const tockArrayView<T,N>& arr)
		:	n(0),sp(arr.data())
	{
	}
	
	///For the receiver:
	inline tockSendableArrayOfBytes(unsigned _n,void* p)
		:	n(_n),dp(p)
	{
	}
	
	//Also for the receiver:
	template <typename T, unsigned N>
	inline explicit tockSendableArrayOfBytes(unsigned _n, const tockArrayView<T,N>& arr)
		:	n(_n),dp(arr.data())
	{
	}
		
	inline void operator=(const tockSendableArrayOfBytes& _src)
	{
		//We use the receiver's byte count:
		memcpy(dp,_src.sp,n);
	}
};

inline void tockSendInt(const csp::Chanout<tockSendableArrayOfBytes>& c, unsigned int n)
{
	c << tockSendableArrayOfBytes(&n);
}

inline void tockRecvInt(const csp::Chanin<tockSendableArrayOfBytes>& c, unsigned int* p)
{
    tockSendableArrayOfBytes d(sizeof(unsigned int),p);
	c >> d;
}

template <typename T, unsigned N>
class tockSendableArray
{
private:
	tockSendableArrayOfBytes aob;
public:
	template <unsigned D>
	inline explicit tockSendableArray(const tockArrayView<T,D>& arr)
		:	aob(N*sizeof(T),arr.data())
	{
	}

	template <unsigned D>
	inline explicit tockSendableArray(const tockArrayView<const T,D>& arr)
		:	aob(arr.data())
	{
	}	
};

template <typename T, unsigned N, unsigned D>
inline void tockSendArray(const csp::Chanout< tockSendableArray<T,N> >& out,const tockArrayView<T,D>& arr)
{
	out << tockSendableArray<T,N>(arr);
}

template <typename T, unsigned N, unsigned D>
inline void tockRecvArray(const csp::Chanin< tockSendableArray<T,N> >& in,const tockArrayView<T,D>& arr)
{
	tockSendableArray<T,N> tsa(arr);
	in >> tsa;
}

template <typename T, unsigned N, unsigned D>
inline void tockSendArray(const csp::Chanout< tockSendableArray<T,N> >& out,const tockArrayView<const T,D>& arr)
{
	out << tockSendableArray<T,N>(arr);
}

inline void tockSendArrayOfBytes(const csp::Chanout<tockSendableArrayOfBytes>& c, const tockSendableArrayOfBytes& b)
{
	c << b;
}

inline void tockRecvArrayOfBytes(const csp::Chanin<tockSendableArrayOfBytes>& c, const tockSendableArrayOfBytes& _b)
{
	//We can't read into the const parameter, so we copy it into a non-const version and read into that.
	//The copying will preserve the pointer inside, so it doesn't cause any problems:
    tockSendableArrayOfBytes b(_b);
	c >> b;
}

template <typename T>
inline void tockInitChanArray(T* pointTo,T** pointFrom,int count)
{
	for (int i = 0;i < count;i++)
		pointFrom[i] = &(pointTo[i]);
}

class StreamWriterByteArray : public csp::CSProcess
{
private:
	std::ostream& out; 	
	csp::Chanin<tockSendableArrayOfBytes> in;
protected:
	virtual void run()
	{
		try
		{
			uint8_t c;
			while (true)
			{
				tockSendableArrayOfBytes aob(1,&c);
				in >> aob;
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
	inline StreamWriterByteArray(std::ostream& _out,const csp::Chanin<tockSendableArrayOfBytes>& _in)
		:	out(_out),in(_in)
	{
	}
};

template <typename T>
class tockList
{
private:
	mutable std::list<T> data;
public:
	inline tockList()
	{
	}
	
	inline explicit tockList(const T& t)
	{
		data.push_back(t);
	}
	
	inline tockList& operator()(const T& t)
	{
		data.push_back(t);
		return *this;
	}
	
	typedef std::list<T>::iterator iterator;
	
	inline iterator beginSeqEach()
	{
		return data.begin();
	}
	
	inline iterator limitIterator()
	{
		return data.end();
	}
	
	inline void endSeqEach()
	{
	}
	
	inline void remove(const iterator& _it)
	{
		data.erase(_it);
	}
	
	//TODO add beginParEach
	//TODO add functions for concatenation
	
	//By default the class acts like a mobile thing:
	inline void operator=(const tockList<T>& _rhs)
	{
		data.clear();
		data.swap(_rhs.data);
	}
	
	class derefTockList
	{
	private:
		tockList<T>* ref;
	public:
		inline explicit derefTockList(tockList<T>* _ref)
			:	ref(_ref)
		{
		}

		//If you dereference both sides, you get a proper copy-assignment:
		void operator=(const derefTockList& _rhs)
		{
			ref->data = _rhs.ref->data;
		}
	};
	
	derefTockList operator*()
	{
		return derefTockList(this);
	}
	
};
