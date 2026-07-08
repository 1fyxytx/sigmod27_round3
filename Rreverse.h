#include <iostream>
#include <string>
#include <vector>
#include <cctype>
#include <algorithm>

bool isMetaChar(char c) {
    return c == '*' || c == '+' || c == '?' || c == '|' ||
           c == '(' || c == ')' || c == '[' || c == ']' ||
           c == '^' || c == '$' || c == '.';
}

// 查找匹配的 '('，考虑转义
int findMatchingParen(const std::string& s, int start, int pos) {
    int count = 1;
    int i = pos;
    while (i > start && count > 0) {
        i--;
        if (s[i] == '\\') {
            i--; // 跳过转义字符
            continue;
        }
        if (s[i] == ')') count++;
        else if (s[i] == '(') count--;
    }
    return i;
}

// 查找匹配的 '['，考虑转义
int findMatchingBracket(const std::string& s, int start, int pos) {
    int count = 1;
    int i = pos;
    while (i > start && count > 0) {
        i--;
        if (s[i] == '\\') {
            i--;
            continue;
        }
        if (s[i] == ']') count++;
        else if (s[i] == '[') count--;
    }
    return i;
}

// 获取指定区间内顶层 '|' 的位置（不在括号或字符类内）
std::vector<int> getTopLevelBars(const std::string& s, int start, int end) {
    std::vector<int> bars;
    int depth = 0;
    bool inCharClass = false;
    for (int i = start; i <= end; ++i) {
        if (s[i] == '\\') {
            ++i; // 跳过转义字符
            continue;
        }
        if (s[i] == '[' && !inCharClass) {
            inCharClass = true;
        } else if (s[i] == ']' && inCharClass) {
            inCharClass = false;
        } else if (!inCharClass) {
            if (s[i] == '(') {
                ++depth;
            } else if (s[i] == ')') {
                --depth;
            } else if (depth == 0 && s[i] == '|') {
                bars.push_back(i);
            }
        }
    }
    return bars;
}

std::string reverseRegexRecursive(const std::string& regex, int start, int end) {
    if (start > end) return "";
    if (start == end) return std::string(1, regex[start]);

    // 1. 处理顶层 '|' 分支
    std::vector<int> bars = getTopLevelBars(regex, start, end);
    if (!bars.empty()) {
        std::string result;
        int prev = start;
        for (int bar : bars) {
            result += reverseRegexRecursive(regex, prev, bar - 1);
            result += '|';
            prev = bar + 1;
        }
        result += reverseRegexRecursive(regex, prev, end);
        return result;
    }

    // 2. 没有顶层 '|'，从右向左扫描处理量词、分组、字符类等
    std::string result;
    int i = end;

    while (i >= start) {
        if (regex[i] == '\\') {
            // 转义字符
            if (i + 1 <= end) {
                result += regex[i];
                result += regex[i + 1];
                i -= 2;
            } else {
                result += regex[i];
                i--;
            }
            continue;
        }

        if (regex[i] == '*' || regex[i] == '+' || regex[i] == '?') {
            // 量词：找到前面的原子
            int atomEnd = i - 1;
            int atomStart = atomEnd;

            if (atomEnd >= start) {
                if (regex[atomEnd] == ')') {
                    atomStart = findMatchingParen(regex, start, atomEnd);
                } else if (regex[atomEnd] == ']') {
                    atomStart = findMatchingBracket(regex, start, atomEnd);
                } else if (regex[atomEnd] == '\\') {
                    atomStart = atomEnd; // 转义字符本身
                } else {
                    // 普通字符，检查是否被转义
                    if (atomEnd - 1 >= start && regex[atomEnd - 1] == '\\') {
                        atomStart = atomEnd - 1;
                    }
                }
            }

            std::string reversedAtom = reverseRegexRecursive(regex, atomStart, atomEnd);
            result += reversedAtom + regex[i];
            i = atomStart - 1;
            continue;
        }

        if (regex[i] == ')') {
            int groupStart = findMatchingParen(regex, start, i);
            std::string inner = reverseRegexRecursive(regex, groupStart + 1, i - 1);
            result += "(" + inner + ")";
            i = groupStart - 1;
            continue;
        }

        if (regex[i] == ']') {
            int classStart = findMatchingBracket(regex, start, i);
            std::string inner = regex.substr(classStart + 1, i - classStart - 1);
            std::reverse(inner.begin(), inner.end());
            result += "[" + inner + "]";
            i = classStart - 1;
            continue;
        }

        // 普通字符
        result += regex[i];
        i--;
    }
    return result;
}

std::string reverseRegex(const std::string& regex) {
    return reverseRegexRecursive(regex, 0, regex.length() - 1);
}

// int main() {
//     std::string tests[] = {
//         "ab*c",      // b*a
//         "a*b*c*",      // ba*
//         "a+b?",     // b?a+
//         "a*b|c*d",    // ba|dc
//         "abcd",    // (ba)*
//         // "a[bc]d",   // d[cb]a
//         // "a\\*b",    // b\\*a
//         // "(a(b(c)*))" // ((c)*ba)
//     };

//     for (const auto& test : tests) {
//         std::cout << "原正则: " << test << "\n";
//         std::cout << "逆序后: " << reverseRegex(test) << "\n\n";
//     }

//     return 0;
// }