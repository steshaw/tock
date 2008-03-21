/*
 * C++CSP support code for Tock programs
 * Copyright (C) 2007, 2008  University of Kent
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

#define occam_stop(pos, nargs, format, args...) \
    do { \
        char buffer[1024]; \
        snprintf(buffer, sizeof(buffer), "Program stopped at %s: " format "\n", pos, ##args); \
        throw StopException(buffer); \
    } while (0)

#include <tock_support.h>

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
	
	///For the receiver:
	inline tockSendableArrayOfBytes(unsigned _n,void* p)
		:	n(_n),dp(p)
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

	//Copy construction has the same behaviour as assignment:
	inline tockList(const tockList<T>& _rhs)
	{
	  *this = _rhs;
	}
	
	inline tockList& operator()(const T& t)
	{
		data.push_back(t);
		return *this;
	}
	
	typedef typename std::list<T>::iterator iterator;
	
	inline iterator beginSeqEach() const
	{
		return data.begin();
	}
	
	inline iterator limitIterator() const
	{
		return data.end();
	}
	
	inline void endSeqEach() const
	{
	}
	
	inline void remove(const iterator& _it)
	{
		data.erase(_it);
	}

	inline unsigned size()
	{
	    return data.size();
	}
	
	//TODO add beginParEach
	//TODO add functions for concatenation

	//By default, the class is mobile, so operator+ adds to this list
	//and effectively blanks the other
	inline tockList<T> operator+(const tockList<T>& _rhs) const
	{
	  data.splice(data.end(), _rhs.data);
	  return *this;
	}
	
	//By default the class acts like a mobile thing:
	inline void operator=(const tockList<T>& _rhs)
	{
		data.clear();
		data.swap(_rhs.data);
	}
	
	class derefTockList
	{
	private:
		tockList<T>* const ref;
	public:
		inline explicit derefTockList(tockList<T>* _ref)
			:	ref(_ref)
		{
		}

		//If you dereference both sides, you get a proper copy-assignment:
		inline void operator=(const derefTockList& _rhs)
		{
			ref->data = _rhs.ref->data;
		}
	};
	
	derefTockList operator*()
	{
		return derefTockList(this);
	}
	
};
