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
#include <list>

#include <termios.h>
#include <unistd.h>

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
		}
		catch (csp::PoisonException& e)
		{
			in.poison();
		}
		out.flush();
	}
public:
	inline StreamWriter(std::ostream& _out,const csp::Chanin<uint8_t>& _in)
		:	out(_out),in(_in)
	{
	}
};

class StreamReader : public csp::CSProcess
{
private:
	std::istream& in;
	csp::Chanout<uint8_t> out;
protected:
	virtual void run()
	{
		try
		{
			tock_configure_terminal(true);
			char c;
			while (true)
			{
				in.get(c);
				out << (uint8_t)c;
			}
		}
		catch (csp::PoisonException& e)
		{
			out.poison();
		}
	}
public:
	inline StreamReader(std::istream& _in,const csp::Chanout<uint8_t>& _out)
		:	in(_in),out(_out)
	{
	}
};

//Exits the whole program when it is run
class LethalProcess : public csp::CSProcess
{
protected:
	void run ()
	{
		//TODO should probably put this in an exit handler instead:
		tock_restore_terminal();
		exit(0);
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

template <typename T, typename U>
inline void tockInitChaninArray(T* pointTo,U* pointFrom,int count)
{
	for (int i = 0;i < count;i++)
	  pointFrom[i] = pointTo[i]->reader();
}

template <typename T, typename U>
inline void tockInitChanoutArray(T* pointTo,U* pointFrom,int count)
{
	for (int i = 0;i < count;i++)
	  pointFrom[i] = pointTo[i]->writer();
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
				if (c == 255)
				{
					out.flush();
				}
				else
				{
					out << c;
				}
			}
		}
		catch (csp::PoisonException& e)
		{
			in.poison();
		}
		out.flush();
	}
public:
	inline StreamWriterByteArray(std::ostream& _out,const csp::Chanin<tockSendableArrayOfBytes>& _in)
		:	out(_out),in(_in)
	{
	}
};

class StreamReaderByteArray : public csp::CSProcess
{
private:
	std::istream& in;
	csp::Chanout<tockSendableArrayOfBytes> out;
protected:
	virtual void run()
	{
		try
		{
			tock_configure_terminal(true);
			char c;
			while (true)
			{
				in.get(c);
				tockSendableArrayOfBytes aob(&c);
				out << aob;
			}
		}
		catch (csp::PoisonException& e)
		{
			out.poison();
		}
	}
public:
	inline StreamReaderByteArray(std::istream& _in,const csp::Chanout<tockSendableArrayOfBytes>& _out)
		:	in(_in),out(_out)
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
		
		/*
		//If you dereference both sides, you get a proper copy-assignment:
		inline void operator=(const derefTockList& _rhs)
		{
			ref->data = _rhs.ref->data;
		}
		*/
		
		inline operator tockList<T>()
		{
			tockList<T> x;
			x.data = ref->data;
			return x;
		}
	};
	
	derefTockList operator*()
	{
		return derefTockList(this);
	}
	
	inline bool operator==(const tockList& _l) const
	{
		if (_l.data.size() != data.size())
			return false;
		
		iterator it, it2;
		for (it = data.begin(), it2 = _l.data.begin(); it != data.end();it++,it2++)
		{
			if (*it == *it2)
			{
				//Fine, continue
			}
			else
			{
				return false;
			}
		}
		return true;
	}
	
	inline bool operator!=(const tockList& _l) const
	{
		return !(*this == _l);
	}
};

class StreamWriterList : public csp::CSProcess
{
private:
	std::ostream& out; 	
	csp::Chanin< tockList<uint8_t> > in;
protected:
	virtual void run()
	{
		try
		{
			tockList<uint8_t> cs;
			while (true)
			{
				in >> cs;
				for (tockList<uint8_t>::iterator it = cs.beginSeqEach();it != cs.limitIterator();it++)
				{
					out << *it;
				}
				out.flush();
			}
		}
		catch (csp::PoisonException& e)
		{
			in.poison();
		}
		out.flush();
	}
public:
	inline StreamWriterList(std::ostream& _out,const csp::Chanin< tockList<uint8_t> >& _in)
		:	out(_out),in(_in)
	{
	}
};


// Time addition and subtraction:

inline csp::Time occam_plus_time (const csp::Time& a, const csp::Time& b, const char *)
{
	return a + b;
}

inline csp::Time occam_minus_time (const csp::Time& a, const csp::Time& b, const char *)
{
	return a - b;
}

// Time intrinsics for Rain:

inline double occam_toSeconds(const csp::Time& val, const char*)
{
	return csp::GetSeconds(val);
}

inline int64_t occam_toMillis(const csp::Time& val, const char*)
{
	return static_cast<int64_t>(1000.0 * csp::GetSeconds(val));
}

inline int64_t occam_toMicros(const csp::Time& val, const char*)
{
	return static_cast<int64_t>(1000000.0 * csp::GetSeconds(val));
}

inline int64_t occam_toNanos(const csp::Time& val, const char*)
{
	return static_cast<int64_t>(1000000000.0 * csp::GetSeconds(val));
}

inline csp::Time occam_fromSeconds(const double val, const char*)
{
	return csp::Seconds(val);
}

inline csp::Time occam_fromMillis(const int64_t val, const char*)
{
	return csp::Seconds(static_cast<double>(val) / 1000.0);
}

inline csp::Time occam_fromMicros(const int64_t val, const char*)
{
	return csp::Seconds(static_cast<double>(val) / 1000000.0);
}

inline csp::Time occam_fromNanos(const int64_t val, const char*)
{
	return csp::Seconds(static_cast<double>(val) / 1000000000.0);
}
