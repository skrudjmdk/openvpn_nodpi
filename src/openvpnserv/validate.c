/*
 *  OpenVPN -- An application to securely tunnel IP networks
 *             over a single TCP/UDP port, with support for SSL/TLS-based
 *             session authentication and key exchange,
 *             packet encryption, packet authentication, and
 *             packet compression.
 *
 *  Copyright (C) 2016-2025 Selva Nair <selva.nair@gmail.com>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License version 2
 *  as published by the Free Software Foundation.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, see <https://www.gnu.org/licenses/>.
 */

#include "validate.h"

#include <lmaccess.h>
#include <shlwapi.h>
#include <pathcch.h>
#include <lm.h>
#include <strsafe.h>

static const WCHAR *white_list[] = {
    L"auth-retry",
    L"config",
    L"log",
    L"log-append",
    L"management",
    L"management-forget-disconnect",
    L"management-hold",
    L"management-query-passwords",
    L"management-query-proxy",
    L"management-signal",
    L"management-up-down",
    L"mute",
    L"setenv",
    L"service",
    L"verb",
    L"pull-filter",
    L"script-security",

    NULL /* last value */
};

static BOOL IsUserInGroup(PSID sid, const PTOKEN_GROUPS groups, const WCHAR *group_name);

static PTOKEN_GROUPS GetTokenGroups(const HANDLE token);

static HRESULT APIENTRY PathCchCanonicalize_(PWSTR pszBuf, size_t cchBuf, PCWSTR pszPath)
{
    if (pszBuf == NULL || cchBuf == 0 || pszPath == NULL)
        return E_INVALIDARG;

    pszBuf[0] = L'\0';

    size_t inputLen = 0;
    HRESULT hr = StringCchLengthW(pszPath, 32768, &inputLen);
    if (FAILED(hr))
        return hr;

    if (inputLen == 0)
    {
        pszBuf[0] = L'\0';
        return S_OK;
    }

    WCHAR temp[32768];
    size_t componentLens[8192];
    size_t compCount = 0;
    size_t used = 0;

    BOOL isUnc = FALSE;
    BOOL isRooted = FALSE;
    size_t i = 0;

    if (inputLen >= 2 && pszPath[0] == L'\\' && pszPath[1] == L'\\')
    {
        isUnc = TRUE;
        isRooted = TRUE;
        if (used + 2 >= 32768) return E_OUTOFMEMORY;
        temp[used++] = L'\\';
        temp[used++] = L'\\';
        i = 2;
        while (i < inputLen && pszPath[i] == L'\\')
            i++;
        size_t s = i;
        while (i < inputLen && pszPath[i] != L'\\')
            i++;
        size_t l = i - s;
        if (l == 0)
            goto fallback;
        if (used + l >= 32768)
            return E_OUTOFMEMORY;
        StringCchCopyNW(temp + used, 32768 - used, pszPath + s, l);
        componentLens[compCount++] = used + l;
        used += l;
        if (i < inputLen && pszPath[i] == L'\\')
            i++;
        else
            goto assemble;
        s = i;
        while (i < inputLen && pszPath[i] != L'\\')
            i++;
        l = i - s;
        if (l == 0)
            goto assemble;
        if (used + 1 + l >= 32768)
            return E_OUTOFMEMORY;
        temp[used++] = L'\\';
        StringCchCopyNW(temp + used, 32768 - used, pszPath + s, l);
        componentLens[compCount++] = used + l;
        used += l;
    }
    else if (inputLen >= 2 && pszPath[1] == L':' &&
             ((pszPath[0] >= L'A' && pszPath[0] <= L'Z') ||
              (pszPath[0] >= L'a' && pszPath[0] <= L'z')))
    {
        if (used + 2 >= 32768)
            return E_OUTOFMEMORY;
        temp[used++] = pszPath[0];
        temp[used++] = L':';
        if (inputLen >= 3 && pszPath[2] == L'\\')
        {
            temp[used++] = L'\\';
            isRooted = TRUE;
        }
        componentLens[compCount++] = used;
        i = (pszPath[2] == L'\\')?3:2;
    }

    while (i < inputLen)
    {
        while (i < inputLen && pszPath[i] == L'\\')
            i++;
        if (i >= inputLen)
            break;
        size_t s = i;
        while (i < inputLen && pszPath[i] != L'\\')
            i++;
        size_t l = i - s;

        if (l == 1 && pszPath[s] == L'.')
            continue;
        if (l == 2 && pszPath[s] == L'.' && pszPath[s + 1] == L'.')
        {
            if (compCount > 0)
            {
                if (isRooted)
                {
                    if (isUnc)
                    {
                        if (compCount <= 2)
                            continue;
                    }
                    else
                    {
                        if (compCount == 1 && used == 3 && temp[1] == L':' && temp[2] == L'\\')
                            continue;
                    }
                }
                compCount--;
                used = (compCount == 0)?0:componentLens[compCount - 1];
            }
            else
            {
                if (used > 0)
                    temp[used++] = L'\\';
                temp[used++] = L'.'; temp[used++] = L'.';
                componentLens[compCount++] = used;
            }
        }
        else
        {
            if (used > 0)
                temp[used++] = L'\\';
            if (used + l >= 32768)
                return E_OUTOFMEMORY;
            StringCchCopyNW(temp + used, 32768 - used, pszPath + s, l);
            componentLens[compCount++] = used + l;
            used += l;
        }
    }

assemble:
    temp[used] = L'\0';

    if (compCount > 0)
    {
        size_t lastStart = (compCount == 1)?0:(componentLens[compCount - 2] + 1);
        size_t lastLen = used - lastStart;

        BOOL hasWildcard = FALSE;
        for (size_t k = 0; k < lastLen; k++)
        {
            if (temp[lastStart + k] == L'*' || temp[lastStart + k] == L'?')
            {
                hasWildcard = TRUE;
                break;
            }
        }

        if (hasWildcard && lastLen > 0)
        {
            size_t lastNonDot = 0;
            BOOL starFound = FALSE;
            for (size_t k = 0; k < lastLen; k++)
            {
                if (temp[lastStart + k] == L'*' || temp[lastStart + k] == L'?')
                    starFound = TRUE;
                if (temp[lastStart + k] != L'.')
                    lastNonDot = k;
            }

            if (starFound)
            {
                if (lastLen >= 2 && temp[lastStart] == L'*' && lastNonDot == 0)
                {
                    BOOL onlyDotsAfterStar = TRUE;
                    for (size_t k = 1; k < lastLen; k++)
                    {
                        if (temp[lastStart + k] != L'.')
                        {
                            onlyDotsAfterStar = FALSE;
                            break;
                        }
                    }
                    if (onlyDotsAfterStar)
                    {
                        if (lastStart + 2 < 32768)
                        {
                            temp[lastStart] = L'*';
                            temp[lastStart + 1] = L'.';
                            temp[lastStart + 2] = L'\0';
                            used = lastStart + 2;
                        }
                    }
                    else if (lastLen >= 3 && lastNonDot >= 2 &&
                             temp[lastStart + lastNonDot] != L'.' &&
                             temp[lastStart + lastNonDot - 1] == L'.')
                    {
                        temp[lastStart + lastNonDot + 1] = L'\0';
                        used = lastStart + lastNonDot + 1;
                    }
                }
                else
                {
                    if (lastNonDot + 1 < lastLen)
                    {
                        temp[lastStart + lastNonDot + 1] = L'\0';
                        used = lastStart + lastNonDot + 1;
                    }
                }
            }
        }
    }

    if (used >= cchBuf)
        return STRSAFE_E_INSUFFICIENT_BUFFER;

    return StringCchCopyW(pszBuf, cchBuf, temp);

fallback:
    if (inputLen >= cchBuf)
        return STRSAFE_E_INSUFFICIENT_BUFFER;
    return StringCchCopyW(pszBuf, cchBuf, pszPath);
}

static HRESULT APIENTRY PathCchCombine_(PWSTR pszPathOut, size_t cchPathOut, PCWSTR pszPathIn, PCWSTR pszPathMore)
{
	if (pszPathOut == NULL || cchPathOut == 0)
		return E_INVALIDARG;

	pszPathOut[0] = L'\0';

	if (pszPathMore == NULL)
	{
		return PathCchCanonicalize_(pszPathOut, cchPathOut, pszPathIn?pszPathIn:L"");
	}

	BOOL isAbsolute = FALSE;
	size_t lenMore = 0;
	HRESULT hr = StringCchLengthW(pszPathMore, STRSAFE_MAX_CCH, &lenMore);
	if (FAILED(hr))
		return hr;

	if (lenMore > 0)
	{
		if (lenMore >= 2 && pszPathMore[0] == L'\\' && pszPathMore[1] == L'\\')
			isAbsolute = TRUE;		
        else if (lenMore >= 3 && pszPathMore[1] == L':' && pszPathMore[2] == L'\\' && ((pszPathMore[0] >= L'A' && pszPathMore[0] <= L'Z') ||  (pszPathMore[0] >= L'a' && pszPathMore[0] <= L'z')))
			isAbsolute = TRUE;		 
	}

	if (isAbsolute)
	{
		return PathCchCanonicalize_(pszPathOut, cchPathOut, pszPathMore);
	}

	WCHAR combined[32768];
	size_t lenIn = 0;

	if (pszPathIn == NULL || pszPathIn[0] == L'\0')
	{
		hr = StringCchCopyW(combined, ARRAYSIZE(combined), pszPathMore);
	}
	else
	{
		hr = StringCchLengthW(pszPathIn, ARRAYSIZE(combined) - 1, &lenIn);
		if (FAILED(hr))
			return hr;

		hr = StringCchCopyW(combined, ARRAYSIZE(combined), pszPathIn);
		if (FAILED(hr))
			return hr;

		if (lenIn > 0 && combined[lenIn - 1] == L'\\')
		{
			BOOL isRoot = FALSE;
			if (lenIn >= 3 && combined[1] == L':' && combined[2] == L'\\')
				isRoot = TRUE;
			else if (lenIn >= 2 && combined[0] == L'\\' && combined[1] == L'\\')
			{
				size_t slashes = 0;
				for (size_t i = 0; i < lenIn; i++)
					if (combined[i] == L'\\') slashes++;
				if (slashes >= 3)
					isRoot = TRUE;
			}

			if (!isRoot)
				combined[lenIn - 1] = L'\0';
		}

		hr = StringCchCatW(combined, ARRAYSIZE(combined), L"\\");
		if (SUCCEEDED(hr))
			hr = StringCchCatW(combined, ARRAYSIZE(combined), pszPathMore);
	}

	if (FAILED(hr))
		return hr;

	return PathCchCanonicalize_(pszPathOut, cchPathOut, combined);
}

/*
 * Check that config path is inside config_dir
 * The logic here is simple: if the path isn't prefixed with config_dir it's rejected
 */
static BOOL
CheckConfigPath(const WCHAR *workdir, const WCHAR *fname, const settings_t *s)
{
    HRESULT res;
    WCHAR config_path[MAX_PATH];

    /* fname = stdin is special: do not treat it as a relative path */
    if (wcscmp(fname, L"stdin") == 0)
    {
        return FALSE;
    }
    /* convert fname to full canonical path */
    if (PathIsRelativeW(fname))
    {
        res = PathCchCombine_(config_path, _countof(config_path), workdir, fname);
    }
    else
    {
        res = PathCchCanonicalize_(config_path, _countof(config_path), fname);
    }

    return res == S_OK && wcsnicmp(config_path, s->config_dir, wcslen(s->config_dir)) == 0;
}


/*
 * A simple linear search meant for a small wchar_t *array.
 * Returns index to the item if found, -1 otherwise.
 */
static int
OptionLookup(const WCHAR *name, const WCHAR *white_list[])
{
    int i;

    for (i = 0; white_list[i]; i++)
    {
        if (wcscmp(white_list[i], name) == 0)
        {
            return i;
        }
    }

    return -1;
}

/*
 * The Administrators group may be localized or renamed by admins.
 * Get the local name of the group using the SID.
 */
static BOOL
GetBuiltinAdminGroupName(WCHAR *name, DWORD nlen)
{
    BOOL b = FALSE;
    PSID admin_sid = NULL;
    DWORD sid_size = SECURITY_MAX_SID_SIZE;
    SID_NAME_USE snu;

    WCHAR domain[MAX_NAME];
    DWORD dlen = _countof(domain);

    admin_sid = malloc(sid_size);
    if (!admin_sid)
    {
        return FALSE;
    }

    b = CreateWellKnownSid(WinBuiltinAdministratorsSid, NULL, admin_sid, &sid_size);
    if (b)
    {
        b = LookupAccountSidW(NULL, admin_sid, name, &nlen, domain, &dlen, &snu);
    }

    free(admin_sid);

    return b;
}

BOOL
IsAuthorizedUser(PSID sid, const HANDLE token, const WCHAR *ovpn_admin_group,
                 const WCHAR *ovpn_service_user)
{
    const WCHAR *admin_group[2];
    WCHAR username[MAX_NAME];
    WCHAR domain[MAX_NAME];
    WCHAR sysadmin_group[MAX_NAME];
    DWORD len = MAX_NAME;
    BOOL ret = FALSE;
    SID_NAME_USE sid_type;

    /* Get username */
    if (!LookupAccountSidW(NULL, sid, username, &len, domain, &len, &sid_type))
    {
        MsgToEventLog(M_SYSERR, L"LookupAccountSid");
        /* not fatal as this is now used only for logging */
        username[0] = '\0';
        domain[0] = '\0';
    }

    /* is this service account? */
    if ((wcscmp(username, ovpn_service_user) == 0) && (wcscmp(domain, L"NT SERVICE") == 0))
    {
        return TRUE;
    }

    if (GetBuiltinAdminGroupName(sysadmin_group, _countof(sysadmin_group)))
    {
        admin_group[0] = sysadmin_group;
    }
    else
    {
        MsgToEventLog(M_SYSERR,
                      L"Failed to get the name of Administrators group. Using the default.");
        /* use the default value */
        admin_group[0] = SYSTEM_ADMIN_GROUP;
    }
    admin_group[1] = ovpn_admin_group;

    PTOKEN_GROUPS token_groups = GetTokenGroups(token);
    for (int i = 0; i < 2; ++i)
    {
        ret = IsUserInGroup(sid, token_groups, admin_group[i]);
        if (ret)
        {
            MsgToEventLog(M_INFO,
                          L"Authorizing user '%ls@%ls' by virtue of membership in group '%ls'",
                          username, domain, admin_group[i]);
            goto out;
        }
    }

out:
    free(token_groups);
    return ret;
}

/**
 * Get a list of groups in token.
 * Returns a pointer to TOKEN_GROUPS struct or NULL on error.
 * The caller should free the returned pointer.
 */
static PTOKEN_GROUPS
GetTokenGroups(const HANDLE token)
{
    PTOKEN_GROUPS groups = NULL;
    DWORD buf_size = 0;

    if (!GetTokenInformation(token, TokenGroups, groups, buf_size, &buf_size)
        && GetLastError() == ERROR_INSUFFICIENT_BUFFER)
    {
        groups = malloc(buf_size);
    }
    if (!groups)
    {
        MsgToEventLog(M_SYSERR, L"GetTokenGroups");
    }
    else if (!GetTokenInformation(token, TokenGroups, groups, buf_size, &buf_size))
    {
        MsgToEventLog(M_SYSERR, L"GetTokenInformation");
        free(groups);
    }
    return groups;
}

/*
 * Find SID from name
 *
 * On input sid buffer should have space for at least sid_size bytes.
 * Returns true on success, false on failure.
 * Suggest: in caller allocate sid to hold SECURITY_MAX_SID_SIZE bytes
 */
static BOOL
LookupSID(const WCHAR *name, PSID sid, DWORD sid_size)
{
    SID_NAME_USE su;
    WCHAR domain[MAX_NAME];
    DWORD dlen = _countof(domain);

    if (!LookupAccountName(NULL, name, sid, &sid_size, domain, &dlen, &su))
    {
        return FALSE; /* not fatal as the group may not exist */
    }
    return TRUE;
}

/**
 * User is in group if the token groups contain the SID of the group
 * of if the user is a direct member of the group. The latter check
 * catches dynamic changes in group membership in the local user
 * database not reflected in the token.
 * If token_groups or sid is NULL the corresponding check is skipped.
 *
 * Using sid and list of groups in token avoids reference to domains so that
 * this could be completed without access to a Domain Controller.
 *
 * Returns true if the user is in the group, false otherwise.
 */
static BOOL
IsUserInGroup(PSID sid, const PTOKEN_GROUPS token_groups, const WCHAR *group_name)
{
    BOOL ret = FALSE;
    DWORD_PTR resume = 0;
    DWORD err;
    BYTE grp_sid[SECURITY_MAX_SID_SIZE];
    int nloop = 0; /* a counter used to not get stuck in the do .. while() */

    /* first check in the token groups */
    if (token_groups && LookupSID(group_name, (PSID)grp_sid, _countof(grp_sid)))
    {
        for (DWORD i = 0; i < token_groups->GroupCount; ++i)
        {
            if (EqualSid((PSID)grp_sid, token_groups->Groups[i].Sid))
            {
                return TRUE;
            }
        }
    }

    /* check user's SID is a member of the group */
    if (!sid)
    {
        return FALSE;
    }
    do
    {
        DWORD nread, nmax;
        LOCALGROUP_MEMBERS_INFO_0 *members = NULL;
        err = NetLocalGroupGetMembers(NULL, group_name, 0, (LPBYTE *)&members, MAX_PREFERRED_LENGTH,
                                      &nread, &nmax, &resume);
        if ((err != NERR_Success && err != ERROR_MORE_DATA))
        {
            break;
        }
        /* If a match is already found, ret == TRUE and the loop is skipped */
        for (DWORD i = 0; i < nread && !ret; ++i)
        {
            ret = EqualSid(members[i].lgrmi0_sid, sid);
        }
        NetApiBufferFree(members);
        /* MSDN says the lookup should always iterate until err != ERROR_MORE_DATA */
    } while (err == ERROR_MORE_DATA && nloop++ < 100);

    if (err != NERR_Success && err != NERR_GroupNotFound)
    {
        SetLastError(err);
        MsgToEventLog(M_SYSERR, L"In NetLocalGroupGetMembers for group '%ls'", group_name);
    }

    return ret;
}

/*
 * Check whether option argv[0] is white-listed. If argv[0] == "--config",
 * also check that argv[1], if present, passes CheckConfigPath().
 * The caller should set argc to the number of valid elements in argv[] array.
 */
BOOL
CheckOption(const WCHAR *workdir, int argc, WCHAR *argv[], const settings_t *s)
{
    /* Do not modify argv or *argv -- ideally it should be const WCHAR *const *, but alas...*/

    if (wcscmp(argv[0], L"--config") == 0 && argc > 1 && !CheckConfigPath(workdir, argv[1], s))
    {
        return FALSE;
    }

    /* option name starts at 2 characters from argv[i] */
    if (OptionLookup(argv[0] + 2, white_list) == -1) /* not found */
    {
        return FALSE;
    }

    return TRUE;
}
