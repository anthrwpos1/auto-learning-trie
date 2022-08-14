#include <codecvt>
#include <fstream>
#include <iostream>
#include <locale>
#include <map>
#include <memory>
#include <random>
#include <set>
#include <unordered_map>

// Класс обрабатывающий текст.
// Поставляет для самообучающегося дерева последовательности букв слов,
// включая символы начала и конца слова, ведет словарь встречающихся слов
// и распределения их длин
class words_proc
{
    const wchar_t* letters =
            L"абвгдеёжзийклмнопрстуфхцчшщъыьэюяАБВГДЕЁЖЗИЙКЛМНОПРСТУФХЦЧШЩЪЫЬЭЮЯ";
    std::unordered_map<wchar_t, int> charindex;
    std::map<int, int> word_lengths; // распределение длин встречающихся слов
    std::map<int, int>
            wl_cums; // кумулятивные суммы длин слов, для вычисления случайной длины
    std::set<std::wstring>
            vocabulary; // словарь учебных слов, для исключения их генерации
    std::mt19937_64* mt = nullptr;
    int wl_sum = 0;
    const wchar_t* current_position = nullptr;
    bool in_word = false;
    std::wstring word;

    const wchar_t* to_another_word_begin(const wchar_t* in_text)
    {
        if (charindex.empty())
            init_index(); // индексируем буквы
        if (in_text == nullptr)
            return nullptr;
        while (find_letter_index(*in_text) == -1)
        {
            if (*in_text == '\0')
                return nullptr;
            in_text++;
        }
        return in_text;
    }

    void init_index()
    {
        for (int i = 0; letters[i]; ++i)
            charindex.insert({letters[i], i});
    }

public:
    const size_t letterssize = wcslen(letters);

    void init_cums()
    {
        // определяем распределение длин слов
        wl_cums.clear();
        wl_sum = 0;
        for (const auto& wlength_item: word_lengths)
        {
            if (wlength_item.first > 1)
            {
                wl_sum = wl_sum + wlength_item.second;
                wl_cums.insert({wl_sum, wlength_item.first});
            }
        }
    }

    int find_letter_index(const wchar_t c)
    {
        auto item = charindex.find(c);
        if (item == charindex.end())
            return -1;
        return item->second;
    }

    void set_text(std::wstring& in_text) { current_position = in_text.c_str(); }

    void set_random_generator(std::mt19937_64* gen) { mt = gen; }

    // получает вплоть до levels индексов букв, включая символы начала и конца
    // слова для слова находящегося в текущей позиции если слово закончилось,
    // автоматически проматывает до ближайшего если слов больше нет, возвращает
    // пустой вектор по ходу дела так-же заполняет словарь встречающихся слов и
    // ведет учет распределения длин слов
    std::vector<int> get_subword(int levels)
    {
        bool begin = !in_word;
        std::vector<int> out;
        if (!in_word)
        {
            current_position = to_another_word_begin(current_position);
            word.clear();
            in_word = true;
            if (current_position == nullptr)
                return out;
            out.push_back(letterssize);
        }
        const wchar_t* position = current_position;
        for (int i = out.size(); i < levels; ++i)
        {
            int index = find_letter_index(*position);
            if (index == -1)
            {
                out.push_back(letterssize + 1);
                in_word = false;
                while (current_position != position)
                {
                    word.push_back(*current_position);
                    ++current_position;
                }
                vocabulary.insert(word);
                auto wl_it = word_lengths.find(word.size());
                if (wl_it == word_lengths.end())
                    word_lengths.insert({word.size(), 1});
                else
                    ++(wl_it->second);
                break;
            }
            out.push_back(index);
            ++position;
        }
        if (!begin)
        {
            word.push_back(*current_position);
            ++current_position;
        }
        return out;
    }

    // возвращает символ означающий данный индекс,
    // а так-же специальные символы начала и конца слова
    wchar_t get_letter(size_t index)
    {
        if (index > letterssize + 1)
            return '\0';
        if (index == letterssize)
            return '{';
        if (index == letterssize + 1)
            return '}';
        return letters[index];
    }

    int get_random_length()
    {
        std::uniform_int_distribution<int> rid{0, wl_sum - 1};
        return wl_cums.upper_bound(rid(*mt))->second; // выбираем длину слова
    }

    // проверяет что такого слова нет в словаре обучающего текста
    bool is_not_vocabular(const std::wstring& test_word)
    {
        bool out = vocabulary.find(test_word) == vocabulary.end();
        return out;
    }
};

// самообучающееся дерево генерирующее слова
// запоминает встречающиеся в обучающем тексте последовательности из заданного
// числа букв включая последовательности попадающиеся в начале и концах слов
// генерирует новые слова методом случайного блуждания по обученному дереву
class wordgenerating_trie
{
    int level = 0; // Уровень дерева
    int counter = 0; // счетчик числа попаданий в данный узел
    std::unique_ptr<wordgenerating_trie[]> elems; // поддеревья
    std::map<int, int> cums; // кумулятивные суммы числа попаданий, для вычисления
    // случайного элемента
    bool cums_valid = false;
    int max_sum = 0;
    const int max_LVL; // число букв в запоминаемых последовательностях
    std::unique_ptr<words_proc> lettersstream_holder;
    words_proc* lettersstream = nullptr;

    // генератор случайных чисел Мерсенна
    std::random_device rd;
    std::seed_seq ss{rd()};
    std::mt19937_64 mt{ss};

    // регистрируем символ в дереве и возвращает поддерево
    wordgenerating_trie* regindex(size_t index)
    {
        if (index > lettersstream->letterssize + 1)
            return nullptr; // проверяем выход за пределы
        if (!elems) // если элементов нет - создаем массив поддеревьев
        {
            elems = std::make_unique<wordgenerating_trie[]>(
                    lettersstream->letterssize + 2);
            for (int i = 0; i < lettersstream->letterssize + 2; ++i)
            {
                elems[i].level = level + 1; // присваиваем им следующий лвл
                elems[i].set_word_proc(lettersstream);
            }
        }
        ++elems[index].counter;     // обновляем счетчик
        return elems.get() + index; // возвращаем поддерево
    }

    // регистрирует последовательность букв
    void regsubseq(const std::vector<int>& indexes)
    {
        wordgenerating_trie* current = this;
        for (int index: indexes)
        {
            current = current->regindex(index); // регистрируем букву, получаем поддерево и идем дальше
        }
    }

    // вычисляет дерево кумулятивных сумм
    void calc_cums()
    {
        if (elems == nullptr)
            return;
        cums.clear();
        max_sum = 0;
        for (int i = 0; i < lettersstream->letterssize; ++i)
        {
            max_sum = max_sum + elems[i].counter;
            cums.insert({max_sum, i});
        }
        cums_valid = true;
    }

    void set_word_proc(words_proc* wp) { lettersstream = wp; }

public:
    // конструктора
    wordgenerating_trie() : max_LVL(4) {}

    explicit wordgenerating_trie(int in_max_LVL) : max_LVL(in_max_LVL) {}

    // создаем дерево из текста
    void regtext(const std::wstring& text, bool verbose)
    {
        cums_valid = false;
        std::wstring text_solid = text;
        if (lettersstream == nullptr)
        {
            lettersstream_holder = std::make_unique<words_proc>();
            lettersstream = lettersstream_holder.get();
            lettersstream->set_text(text_solid);
            lettersstream->set_random_generator(&mt);
        }
        std::vector<int> subseq = lettersstream->get_subword(max_LVL);
        while (!subseq.empty())
        {
            regsubseq(subseq);
            subseq = lettersstream->get_subword(max_LVL);
        }
    }

    // возвращает поддерево из заданного префикса
    wordgenerating_trie* get_subtrie(bool is_begin, const wchar_t* initial)
    {
        if (!elems)
            return nullptr; // конечный узел, элементов нет
        if (is_begin)
        { // проверяем есть ли в данном дереве символ начала слова
            if (elems[lettersstream->letterssize].counter == 0)
                return nullptr;
            return elems[lettersstream->letterssize].get_subtrie(false, initial);
        }
        if (*initial == '\0')
            return this;
        int index = lettersstream->find_letter_index(
                *initial); // проверяем, есть ли такая буква вообще
        if (index == -1)
            return nullptr;
        if (elems[index].counter == 0)
            return nullptr; // проверяем есть ли такая буква в данном узле
        return elems[index].get_subtrie(false, initial + 1);
    }

    // возвращает индекс случайного символа из данного поддерева с учетом их
    // частоты в обучающей выборке
    int get_random_index()
    {
        if (!cums_valid)
        {
            calc_cums();
            lettersstream->init_cums();
        }
        if (max_sum <= 0)
            return -1;
        std::uniform_int_distribution<int> uid{0, max_sum - 1};
        return cums.upper_bound(uid(mt))->second;
    }

    // проверяет, что текущий префикс встречался в качестве конца слова
    bool is_contains_EOW()
    {
        if (elems == nullptr)
            return false;
        return elems[lettersstream->letterssize + 1].counter > 0;
    }

    // рекурсивно обходит дерево выводя в поток вывода все его ветки
    void show(std::wostream& sout, std::wstring& prefix) const
    {
        if (elems == nullptr)
        {
            sout << prefix << L", ";
            return;
        }
        for (int i = 0; i < lettersstream->letterssize + 2; ++i)
        {
            if (elems[i].counter > 0)
            {
                prefix.push_back(lettersstream->get_letter(i));
                elems[i].show(sout, prefix);
                prefix.pop_back();
                if (prefix.length() == 0)
                    sout << std::endl;
            }
        }
    }

    friend std::wostream& operator<<(std::wostream& sout,
                                     const wordgenerating_trie& t)
    {
        std::wstring temp_string;
        t.show(sout, temp_string);
        return sout;
    }

    // пытается сгенерировать псевдослучайное слово
    std::wstring try_to_generate_word(int wordsize)
    {
        int letternum = 0; // текущий номер генерируемой буквы
        if (elems == nullptr)
            return L"";
        if (wordsize <= 0)
            return L"";
        wordgenerating_trie* current =
                elems.get() +
                lettersstream->letterssize; // получаем поддерево от начала слова
        std::wstring out_string;
        std::wstring current_prefix;
        while (current->level < max_LVL - 1)
        {
            int e = current->get_random_index(); // получаем букву
            if (e == -1)
                return L"";
            out_string.push_back(lettersstream->get_letter(e));
            current_prefix.push_back(lettersstream->get_letter(e));
            if (current->elems == nullptr)
                return L"";
            current = current->elems.get() + e;
            ++letternum;
            if (letternum == wordsize)
                break;
        }
        bool still_begin =
                true; // флаг того что сейчас будет итерация с начала слова
        while (letternum < wordsize) // получаем остальные буквы
        {
            current = get_subtrie(still_begin, current_prefix.c_str());
            if (current == nullptr)
                return L"";
            if (current->elems == nullptr)
                return L"";
            int e = current->get_random_index();
            if (e == -1)
                return L"";
            out_string.push_back(lettersstream->get_letter(e));
            if (!still_begin)
                current_prefix.erase(current_prefix.begin());
            current_prefix.push_back(lettersstream->get_letter(e));
            still_begin = false;
            if (current->elems == nullptr)
                return L"";
            ++letternum;
        }
        current = get_subtrie(still_begin, current_prefix.c_str());
        if (current == nullptr)
            return L"";
        if (current->elems == nullptr)
            return L"";
        if (current->is_contains_EOW())
            return out_string;
        return L"";
    }

    // усердно генерировать слово длиной length пока не получится (try_max_times
    // раз максимум) length = -1 - генерировать слово случайной длины в
    // соответствии с длинами слов в обучающем тексте
    std::wstring generate_word(int try_max_times, int length)
    {
        if (!cums_valid)
        {
            calc_cums();
            lettersstream->init_cums();
        }
        if (length == -1)
            length = lettersstream->get_random_length();
        std::wstring out_string;
        if (length < 2)
            return L""; // слова из одной или нуля букв не генерируем
        int m = 0;
        while (out_string.empty()) // пытаемся сгенерировать слово пока не получится
        {
            out_string = try_to_generate_word(length);
            if (++m > try_max_times)
                return L""; // если долго не получается
        }
        return out_string;
    }

    // Генерирует вплоть до words_num случайных слов длиной lengths.
    // lengths = -1 - генерирует слова случайной длины в соответствии с длинами
    // слов в обучающем тексте max_times_to_gen_single - число попыток
    // сгенерировать каждое слово
    std::vector<std::wstring> generate_unique_words(int words_num, int lengths,
                                                    int max_times_to_gen_single)
    {
        // сюда будем складывать нагенерированные слова
        std::set<std::wstring> generated;
        std::vector<std::wstring> generated_unsorted;
        int n = 0;

        while (true)
        {
            std::wstring out_string = generate_word(max_times_to_gen_single, lengths);
            if ((generated.find(out_string) == generated.end()) &&
                (lettersstream->is_not_vocabular(out_string)))
            {
                generated.insert(out_string);
                generated_unsorted.push_back(out_string);
            }
            if (++n > words_num)
                break; // сколько слов нагенерировать
        }
        return generated_unsorted;
    }
};

// разбивает аргумент командной строки на часть до и после символа равно
void get_arg(const char* in_arg, std::string* key, std::string* val)
{
    if (in_arg == nullptr)
        return;
    const char* eq = in_arg;
    while (*eq != '=')
    {
        if (*eq == '\0')
            break;
        ++eq;
    }
    if (key != nullptr)
    {
        key->clear();
        for (const char* t = in_arg; t < eq; ++t)
        {
            key->push_back(*t);
        }
    }
    if (val != nullptr)
    {
        val->clear();
        for (const char* t = eq + 1; *t != '\0'; ++t)
        {
            val->push_back(*t);
        }
    }
}

int main(int argn, char** args)
{
    setlocale(LC_ALL, "ru_RU.utf8"); // настраиваем отображение символов
    std::wstring_convert<std::codecvt_utf8<wchar_t>, wchar_t> converter;
    int lvl_max = 4;
    int iter_max = 100;
    int words = 100;
    int lengths = -1;
    bool verbose = false;
    int columnsize = 21;
    std::ostream* sout = &std::cout;
    std::fstream fout;
    std::string filename = "file.txt";
    for (int i = 1; i < argn; ++i)
    {
        std::string key, val;
        get_arg(args[i], &key, &val);
        if (key == "lvl")
            lvl_max = std::stoi(val);
        else if (key == "iter_max")
            iter_max = std::stoi(val);
        else if (key == "words")
            words = std::stoi(val);
        else if (key == "lengths")
            lengths = std::stoi(val);
        else if (key == "verbose")
            verbose = true;
        else if (key == "column")
            columnsize = std::stoi(val);
        else if (key == "in")
            filename = val;
        else if (key == "out")
        {
            fout = std::fstream{val, std::fstream::out | std::fstream::binary};
            sout = &fout;
        } else
        {
            std::wcout << L"usage: key=value\n"
                          L"keys     | actions\n"
                          L"---------|------------------------------\n"
                          L"lvl      | tree height,\n"
                          L"iter_max | tries to generate single word,\n"
                          L"words    | words to generate,\n"
                          L"lengths  | length of generated words,\n"
                          L"column   | set column size\n"
                          L"in       | input filename,\n"
                          L"out      | output filename,\n"
                          L"verbose  | show trie"
                       << std::endl;
            return 0;
        }
    }

    wordgenerating_trie t{lvl_max};
    std::fstream fin(filename,
                     std::fstream::in |
                     std::fstream::binary); // текстовый файл для обучения
    if (!fin)
    {
        std::cerr << "Попытка прочитать файл " << filename
                  << " не удалась, походу файла нет." << std::endl;
        return 1;
    }
    // определяем размер файла
    fin.seekg(0, std::ios_base::end);
    auto length = fin.tellg();
    fin.seekg(0, std::ios_base::beg);

    // создаем хранилище под содержимое, вычитываем и преобразуем в строку wstring
    char* bytes = new char[length];
    fin.read(bytes, length);
    std::wstring text{converter.from_bytes(bytes, bytes + length - 1)};
    delete[] bytes;

    // обучаем дерево
    t.regtext(text, verbose);
    if (verbose)
    {
        std::wcout << t << std::endl;
    }

    int n1 = 0;
    for (auto& s:
            t.generate_unique_words(words, lengths, iter_max))
    {
        if ((++n1) % (200 / columnsize) == 0)
            (*sout) << std::endl;
        (*sout) << converter.to_bytes(s);
        for (int n2 = s.size(); n2 < columnsize; ++n2)
            (*sout) << ' ';
    }
    (*sout) << std::endl;
    return 0;
}
